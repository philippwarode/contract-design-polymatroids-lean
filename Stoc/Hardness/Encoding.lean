-- stamp r5 2026-11-02
import Stoc.Hardness.CutForms

/-!
# Encoding lengths: the bit model of Appendix C

The bit model of the STOC version's hardness appendix. `def:cutform` (`stoc-sections/
appD-hardness.tex:98-104`) defines `𝒞_cut` as "the class of instances `(f, m, β)` with
`m, β ∈ ℚ^E_{>0}` for which `f` is a rank function given by a cut form, encoded by the cut form,
`m` and `β` in binary", and the opening of Appendix C.8 (`sec:D-npcomplete`) before `lem:exactbr`
(lines 1791-1797) defines the encoding lengths, with the rules at the start of the proof of
`lem:exactbr` (lines 1810-1812).

* `InZ N x` (`x ∈ (1/N)ℤ`) and `Bits B x` (magnitude and a denominator at most `2^B`): the notation
  of the proof of `lem:sizes`, with the rules for sums, products and quotients.
* `enc`: "The encoding length of a rational number `u/v`, with coprime `u ∈ ℤ` and `v ∈ ℤ_{>0}`, is
  `⟨u/v⟩ := 1 + ⌈log₂(|u| + 1)⌉ + ⌈log₂(v + 1)⌉`."
* The rules: "A product or a quotient of rationals has encoding length at most the sum of their
  encoding lengths, and a sum at most twice the sum of their encoding lengths, as one sees by
  writing the terms over the product of their denominators" (`enc_mul`, `enc_div`, `enc_add`,
  `enc_sum_le_two_mul`, with `enc_sum_le` for a sum of any number of terms), and "Every rational
  `u/v` as above satisfies `|u| < 2^{⟨u/v⟩}` and `v < 2^{⟨u/v⟩}`" (`natAbs_num_lt`, `den_lt`).
* `RatInst`: an encoded instance by its data, arcs `D` on `E` with rational capacities, rational
  weights (the cut form `(D, cap, ω)`), and rational rewards and curvatures; `RatInst.f`: the
  function `cut_D + ω` of the data (`eq:cutform`); `RatInst.IsCutForm`: the data is a cut form (no
  loops, nonnegative capacities), and `RatInst.form` is that cut form; `RatInst.encI` is `⟨I⟩`,
  "the sum of the encoding lengths of the capacities, weights, rewards and curvatures of `I`, which
  is at most the encoding length of `I`" (the encoding length of `I` itself, with its digraph, is
  not defined); `RatInst.InCcut`: the encoded instance lies in `𝒞_cut`, and `RatInst.inCcut_iff`:
  `lem:cutforms`(b) for the data, the paper's checks in its order, `|D|` tests of end points and
  `|D| + 3|E|` comparisons of rationals ("In particular, membership in `𝒞_cut` is decided in
  polynomial time").
* The values: "Every value `f(S) = cut_D(S) + ω(S)` is a sum of distinct capacities and weights,
  and `t(S)` and `β⁻¹(S)` are sums of distinct quotients `m_e/β_e` and `1/β_e`, so all three have
  encoding length at most `2⟨I⟩`" (`RatInst.enc_fQ_le`, `RatInst.enc_tQ_le`,
  `RatInst.enc_binvQ_le`), and "`n ≤ ⟨I⟩`, as every reward has encoding length at least `1`" (the
  proof of membership in NP, `RatInst.card_le_encI`).
* From explicit bounds to encoding lengths (not in the paper): a number with `Bits B` is a rational
  of encoding length at most `3B + 3` (`exists_rat_of_bits`), and a real instance with a cut form
  whose numbers all have `Bits B` is a `RatInst` whose data is a cut form
  (`exists_ratInst_of_bits`).

The encoding itself, the strings of bits, is not formalised: the paper uses only its length.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### Rationals with bounded denominators (not in the paper) -/

/-- `x ∈ (1/N)ℤ`: `N x` is an integer (the notation `x ∈ (1/N)ℤ` of the proof of `lem:sizes`). -/
def InZ (N x : ℝ) : Prop := ∃ z : ℤ, N * x = z

namespace InZ

variable {N N' x y : ℝ}

lemma zero : InZ N 0 := ⟨0, by simp⟩

lemma add (hx : InZ N x) (hy : InZ N y) : InZ N (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by push_cast; rw [← ha, ← hb]; ring⟩

lemma neg (hx : InZ N x) : InZ N (-x) := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨-a, by push_cast; rw [← ha]; ring⟩

lemma sub (hx : InZ N x) (hy : InZ N y) : InZ N (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

lemma zmul (n : ℤ) (hx : InZ N x) : InZ N (n * x) := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨n * a, by push_cast; rw [← ha]; ring⟩

/-- A coarser denominator: if `N' = cN` with `c ∈ ℤ`, then `(1/N)ℤ ⊆ (1/N')ℤ`. -/
lemma mono (hx : InZ N x) (c : ℤ) (hN : N' = c * N) : InZ N' x := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨c * a, by rw [hN]; push_cast; rw [← ha]; ring⟩

lemma mul (hx : InZ N x) (hy : InZ N' y) : InZ (N * N') (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a * b, by push_cast; rw [← ha, ← hb]; ring⟩

lemma int (n : ℤ) : InZ 1 n := ⟨n, by simp⟩

lemma nat (n : ℕ) : InZ 1 n := ⟨n, by simp⟩

lemma of_eq (hx : InZ N x) (h : x = y) : InZ N y := h ▸ hx

lemma sum {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ s, InZ N (f i)) :
    InZ N (∑ i ∈ s, f i) :=
  Finset.sum_induction f (InZ N) (fun _ _ ha hb => ha.add hb) zero h

/-- Division by a nonzero integer `c`: `(1/N)ℤ / c ⊆ (1/(Nc))ℤ`. -/
lemma div_int (hx : InZ N x) (c : ℤ) (hc : (c : ℝ) ≠ 0) : InZ (N * c) (x / c) := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by rw [← ha]; field_simp⟩

end InZ

/-- The proof of `lem:sizes`: "A rational number has `O(k + log μ^in_k)` bits if its magnitude and
its denominator are at most `2^{O(k+log μ^in_k)}`." `Bits B x`: `|x| ≤ 2^B`, and `x ∈ (1/n)ℤ` for
a positive integer `n ≤ 2^B`. -/
def Bits (B : ℕ) (x : ℝ) : Prop := |x| ≤ 2 ^ B ∧ ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 2 ^ B ∧ InZ n x

namespace Bits

variable {B B' : ℕ} {x y : ℝ}

lemma mono (hx : Bits B x) (h : B ≤ B') : Bits B' x := by
  obtain ⟨h1, n, hn, hnB, hz⟩ := hx
  have : (2 : ℝ) ^ B ≤ 2 ^ B' := pow_le_pow_right₀ (by norm_num) h
  exact ⟨h1.trans this, n, hn, hnB.trans this, hz⟩

/-- A product of two numbers of at most `B` bits has at most `2B` bits (not in the paper: the
"`O(1)` arithmetic operations" of the proof of `lem:sizes`). -/
lemma mul (hx : Bits B x) (hy : Bits B y) : Bits (2 * B) (x * y) := by
  obtain ⟨h1, n, hn, hnB, hz⟩ := hx
  obtain ⟨h1', n', hn', hnB', hz'⟩ := hy
  refine ⟨?_, n * n', Nat.mul_pos hn hn', ?_, ?_⟩
  · rw [abs_mul, two_mul, pow_add]
    exact mul_le_mul h1 h1' (abs_nonneg _) (by positivity)
  · push_cast
    rw [two_mul, pow_add]
    exact mul_le_mul hnB hnB' (by positivity) (by positivity)
  · push_cast
    exact hz.mul hz'

/-- A sum of two numbers of at most `B` bits has at most `2B + 1` bits (not in the paper, as
`mul`). -/
lemma add (hx : Bits B x) (hy : Bits B y) : Bits (2 * B + 1) (x + y) := by
  obtain ⟨h1, n, hn, hnB, hz⟩ := hx
  obtain ⟨h1', n', hn', hnB', hz'⟩ := hy
  have h2 : (2 : ℝ) ^ B ≤ 2 ^ (2 * B) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨?_, n * n', Nat.mul_pos hn hn', ?_, ?_⟩
  · calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ 2 ^ B + 2 ^ B := add_le_add h1 h1'
      _ ≤ 2 ^ (2 * B + 1) := by rw [pow_succ]; linarith
  · push_cast
    calc (n : ℝ) * n' ≤ 2 ^ B * 2 ^ B := mul_le_mul hnB hnB' (by positivity) (by positivity)
      _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]
      _ ≤ 2 ^ (2 * B + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  · have hx' : InZ ((n : ℝ) * n') x := hz.mono n' (by push_cast; ring)
    have hy' : InZ ((n : ℝ) * n') y := hz'.mono n (by push_cast; ring)
    push_cast
    exact hx'.add hy'

lemma neg (hx : Bits B x) : Bits B (-x) := by
  obtain ⟨h1, n, hn, hnB, hz⟩ := hx
  exact ⟨by rwa [abs_neg], n, hn, hnB, hz.neg⟩

lemma sub (hx : Bits B x) (hy : Bits B y) : Bits (2 * B + 1) (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- A quotient of two numbers of at most `B` bits, the divisor nonzero, has at most `3B` bits (not
in the paper, as `mul`): if `y = z'/n'` with an integer `z' ≠ 0`, then `|y| ≥ 1/n' ≥ 2^{−B}`, so
`|x/y| ≤ 2^{2B}`, and `x/y ∈ (1/(n|z'|))ℤ` with `n|z'| = n n'|y| ≤ 2^{3B}`. -/
lemma div (hx : Bits B x) (hy : Bits B y) (hy0 : y ≠ 0) : Bits (3 * B) (x / y) := by
  obtain ⟨h1, n, hn, hnB, ⟨a, ha⟩⟩ := hx
  obtain ⟨h1', n', hn', hnB', ⟨b, hb⟩⟩ := hy
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0' : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_eq_zero] at hb
    rcases hb with h | h
    · exact hn0'.ne' h
    · exact hy0 h
  have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hb0
  have hyb : |y| = |(b : ℝ)| / n' := by
    rw [eq_div_iff hn0'.ne', ← hb, abs_mul, abs_of_pos hn0']
    ring
  have h2B : (2 : ℝ) ^ (3 * B) = 2 ^ B * 2 ^ B * 2 ^ B := by rw [← pow_add, ← pow_add]; ring_nf
  have hpos : (0 : ℝ) < 2 ^ B := by positivity
  refine ⟨?_, n * b.natAbs, Nat.mul_pos hn (Int.natAbs_pos.2 hb0), ?_, ?_⟩
  · -- `|x/y| = |x| n'/|b| ≤ 2^B 2^B`
    rw [abs_div, hyb, div_div_eq_mul_div, h2B]
    calc |x| * n' / |(b : ℝ)| ≤ |x| * n' := div_le_self (by positivity) hb1
      _ ≤ 2 ^ B * 2 ^ B := mul_le_mul h1 hnB' hn0'.le hpos.le
      _ ≤ 2 ^ B * 2 ^ B * 2 ^ B := le_mul_of_one_le_right (by positivity)
          (one_le_pow₀ (by norm_num))
  · -- `n|b| = n n'|y| ≤ 2^B 2^B 2^B`
    have hbn : ((b.natAbs : ℕ) : ℝ) = |y| * n' := by
      rw [Nat.cast_natAbs, Int.cast_abs, hyb, div_mul_cancel₀ _ hn0'.ne']
    rw [Nat.cast_mul, hbn, h2B]
    calc (n : ℝ) * (|y| * n') ≤ 2 ^ B * (2 ^ B * 2 ^ B) :=
          mul_le_mul hnB (mul_le_mul h1' hnB' hn0'.le hpos.le) (by positivity) hpos.le
      _ = 2 ^ B * 2 ^ B * 2 ^ B := by ring
  · -- `n|b| · x/y = ±a n'`
    have hy' : y = b / n' := by rw [eq_div_iff hn0'.ne', ← hb]; ring
    have hx' : x = a / n := by rw [eq_div_iff hn0.ne', ← ha]; ring
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
    rcases lt_or_gt_of_ne hb0 with h | h
    · refine ⟨-(a * n'), ?_⟩
      have hab : ((b.natAbs : ℕ) : ℝ) = -(b : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]
      rw [Nat.cast_mul, hab, hx', hy']
      field_simp
      push_cast
      ring
    · refine ⟨a * n', ?_⟩
      have hab : ((b.natAbs : ℕ) : ℝ) = (b : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast h)]
      rw [Nat.cast_mul, hab, hx', hy']
      field_simp
      push_cast
      ring

end Bits

/-! ### Encoding lengths of rationals -/

/-- The encoding length of a rational number `u/v`, with coprime `u ∈ ℤ` and `v ∈ ℤ_{>0}`:
`⟨u/v⟩ := 1 + ⌈log₂(|u| + 1)⌉ + ⌈log₂(v + 1)⌉` (`stoc-sections/appD-hardness.tex:1791-1794`; "This
is one bit less than the encoding length of [GLS88, §1.3], which changes only constants"). Here
`x.num` and `x.den` are the coprime numerator and the positive denominator of `x`, and
`⌈log₂ n⌉ = Nat.clog 2 n`. -/
def enc (x : ℚ) : ℕ := 1 + Nat.clog 2 (x.num.natAbs + 1) + Nat.clog 2 (x.den + 1)

/-- `⌈log₂(ab)⌉ ≤ ⌈log₂ a⌉ + ⌈log₂ b⌉` (not in the paper). -/
lemma clog_mul_le (a b : ℕ) : Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  rw [Nat.clog_le_iff_le_pow (by norm_num), pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) a) (Nat.le_pow_clog (by norm_num) b)

/-- `⌈log₂ ∏_i a_i⌉ ≤ ∑_i ⌈log₂ a_i⌉` (not in the paper). -/
lemma clog_prod_le {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    Nat.clog 2 (∏ i ∈ s, a i) ≤ ∑ i ∈ s, Nat.clog 2 (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj]
    exact (clog_mul_le _ _).trans (Nat.add_le_add_left ih _)

/-- `⌈log₂(2^a + 1)⌉ ≤ a + 1` (not in the paper). -/
lemma clog_two_pow_add_one_le (a : ℕ) : Nat.clog 2 (2 ^ a + 1) ≤ a + 1 := by
  rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ]
  have := Nat.one_le_two_pow (n := a)
  omega

/-- Every encoding length is at least `2`, as the denominator takes at least one bit (not in the
paper). -/
lemma two_le_enc (x : ℚ) : 2 ≤ enc x := by
  have := Nat.clog_pos (b := 2) (n := x.den + 1) (by norm_num) (by have := x.den_pos; omega)
  unfold enc
  omega

/-- "Every rational `u/v` as above satisfies `|u| < 2^{⟨u/v⟩}` …" (the proof of `lem:exactbr`,
`stoc-sections/appD-hardness.tex:1811`). -/
lemma natAbs_num_lt (x : ℚ) : x.num.natAbs < 2 ^ enc x := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (x.num.natAbs + 1)
  have h2 : 2 ^ Nat.clog 2 (x.num.natAbs + 1) ≤ 2 ^ enc x :=
    Nat.pow_le_pow_right (by norm_num) (by unfold enc; omega)
  omega

/-- "… and `v < 2^{⟨u/v⟩}`." (the proof of `lem:exactbr`, line 1811). -/
lemma den_lt (x : ℚ) : x.den < 2 ^ enc x := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (x.den + 1)
  have h2 : 2 ^ Nat.clog 2 (x.den + 1) ≤ 2 ^ enc x :=
    Nat.pow_le_pow_right (by norm_num) (by unfold enc; omega)
  omega

/-- If `x = a/b` with integers `a` and `b > 0`, then the coprime numerator and denominator of `x`
are at most `|a|` and `b` (not in the paper). -/
lemma natAbs_num_le_of_eq_div {x : ℚ} {a : ℤ} {b : ℕ} (hb : 0 < b) (hx : x = a / b) :
    x.num.natAbs ≤ a.natAbs ∧ x.den ≤ b := by
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hx' : x = Rat.divInt a b := by rw [Rat.divInt_eq_div, Int.cast_natCast]; exact hx
  constructor
  · rcases eq_or_ne a 0 with rfl | ha
    · simp [hx']
    · rw [hx']
      exact Nat.le_of_dvd (Int.natAbs_pos.2 ha) (Int.natAbs_dvd_natAbs.2 (Rat.num_dvd a hb'))
  · rw [hx']
    exact Nat.le_of_dvd hb (by exact_mod_cast Rat.den_dvd a b)

/-- The encoding length of `a/b` for integers `a` and `b > 0` (not in the paper): at most
`1 + ⌈log₂(|a| + 1)⌉ + ⌈log₂(b + 1)⌉`. -/
lemma enc_le_of_eq_div {x : ℚ} {a : ℤ} {b : ℕ} (hb : 0 < b) (hx : x = a / b) :
    enc x ≤ 1 + Nat.clog 2 (a.natAbs + 1) + Nat.clog 2 (b + 1) := by
  obtain ⟨h1, h2⟩ := natAbs_num_le_of_eq_div hb hx
  have c1 := Nat.clog_mono_right 2 (Nat.add_le_add_right h1 1)
  have c2 := Nat.clog_mono_right 2 (Nat.add_le_add_right h2 1)
  unfold enc
  omega

/-- The encoding length of an integer: `⟨z⟩ = 2 + ⌈log₂(|z| + 1)⌉` (not in the paper). -/
lemma enc_intCast (z : ℤ) : enc z = 2 + Nat.clog 2 (z.natAbs + 1) := by
  have h : Nat.clog 2 (1 + 1) = 1 := by
    have h2 := Nat.clog_pow 2 1 (by norm_num)
    rwa [pow_one] at h2
  unfold enc
  rw [Rat.num_intCast, Rat.den_intCast, h]
  omega

/-- `⟨−x⟩ = ⟨x⟩` (not in the paper). -/
lemma enc_neg (x : ℚ) : enc (-x) = enc x := by
  unfold enc
  rw [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg]

/-- `⟨1/x⟩ = ⟨x⟩` for `x ≠ 0`, and `⟨0⁻¹⟩ = ⟨0⟩` (not in the paper: numerator and denominator
change places). -/
lemma enc_inv (x : ℚ) : enc x⁻¹ = enc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hn : x.num ≠ 0 := Rat.num_ne_zero.2 hx
    unfold enc
    rw [Rat.num_inv, Rat.den_inv_of_ne_zero hx, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn,
      one_mul, Int.natAbs_natCast]
    omega

/-- "A product … of rationals has encoding length at most the sum of their encoding lengths …"
(the proof of `lem:exactbr`, line 1810). -/
lemma enc_mul (x y : ℚ) : enc (x * y) ≤ enc x + enc y := by
  have h := enc_le_of_eq_div (x := x * y) (a := x.num * y.num) (b := x.den * y.den)
    (Nat.mul_pos x.den_pos y.den_pos) (by
      push_cast
      rw [← div_mul_div_comm, Rat.num_div_den, Rat.num_div_den])
  have e1 : (x.num * y.num).natAbs + 1 ≤ (x.num.natAbs + 1) * (y.num.natAbs + 1) := by
    rw [Int.natAbs_mul, add_one_mul, mul_add_one]
    omega
  have e2 : x.den * y.den + 1 ≤ (x.den + 1) * (y.den + 1) := by
    rw [add_one_mul, mul_add_one]
    omega
  have c1 := (Nat.clog_mono_right 2 e1).trans (clog_mul_le _ _)
  have c2 := (Nat.clog_mono_right 2 e2).trans (clog_mul_le _ _)
  unfold enc at h ⊢
  omega

/-- "… or a quotient …" (the proof of `lem:exactbr`, line 1810). -/
lemma enc_div (x y : ℚ) : enc (x / y) ≤ enc x + enc y := by
  rw [div_eq_mul_inv]
  exact (enc_mul _ _).trans (by rw [enc_inv])

/-- The weight `w(x) = ⌈log₂(|u| + v)⌉ + ⌈log₂ v⌉` of `x = u/v`, which bounds the contribution of a
term to a sum written over the product of the denominators (not in the paper). -/
def wt (x : ℚ) : ℕ := Nat.clog 2 (x.num.natAbs + x.den) + Nat.clog 2 x.den

/-- `w(x) + 2 ≤ 2⟨x⟩` (not in the paper). -/
lemma wt_add_two_le (x : ℚ) : wt x + 2 ≤ 2 * enc x := by
  have e1 : x.num.natAbs + x.den ≤ (x.num.natAbs + 1) * (x.den + 1) := by
    rw [add_one_mul, mul_add_one]
    omega
  have c1 := (Nat.clog_mono_right 2 e1).trans (clog_mul_le _ _)
  have c2 := Nat.clog_mono_right 2 (Nat.le_add_right x.den 1)
  unfold wt enc
  omega

/-- A rational with `|u| + v ≤ P` and `v ≤ Q` has encoding length at most
`2 + ⌈log₂ P⌉ + ⌈log₂ Q⌉` (not in the paper). -/
lemma enc_le_of_le (x : ℚ) {P Q : ℕ} (hP : x.num.natAbs + x.den ≤ P) (hQ : x.den ≤ Q) :
    enc x ≤ 2 + Nat.clog 2 P + Nat.clog 2 Q := by
  have hd := x.den_pos
  have c1 : Nat.clog 2 (x.num.natAbs + 1) ≤ Nat.clog 2 P := Nat.clog_mono_right 2 (by omega)
  have c2 : Nat.clog 2 (x.den + 1) ≤ Nat.clog 2 (2 * Q) := Nat.clog_mono_right 2 (by omega)
  have c3 : Nat.clog 2 (2 * Q) ≤ 1 + Nat.clog 2 Q := by
    refine (clog_mul_le 2 Q).trans ?_
    have h2 := Nat.clog_pow 2 1 (by norm_num)
    rw [pow_one] at h2
    rw [h2]
  unfold enc
  omega

/-- Writing a sum over the product of the denominators: `|u| + v` of `x + y` is at most the product
of those of `x` and `y`, and the denominator of `x + y` at most the product of theirs (not in the
paper: the argument of the rule for sums, `stoc-sections/appD-hardness.tex:1810`). -/
lemma add_numDen_le (x y : ℚ) :
    (x + y).num.natAbs + (x + y).den ≤ (x.num.natAbs + x.den) * (y.num.natAbs + y.den) ∧
    (x + y).den ≤ x.den * y.den := by
  have hx : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_pos.ne'
  have hy : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_pos.ne'
  obtain ⟨h1, h2⟩ := natAbs_num_le_of_eq_div (x := x + y)
    (a := x.num * y.den + y.num * x.den) (b := x.den * y.den) (Nat.mul_pos x.den_pos y.den_pos)
    (by
      push_cast
      conv_lhs => rw [← Rat.num_div_den x, ← Rat.num_div_den y]
      rw [div_add_div _ _ hx hy]
      ring)
  refine ⟨?_, h2⟩
  have h3 : (x.num * y.den + y.num * x.den).natAbs ≤
      x.num.natAbs * y.den + y.num.natAbs * x.den := by
    refine (Int.natAbs_add_le _ _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  have h4 : x.num.natAbs * y.den + y.num.natAbs * x.den + x.den * y.den ≤
      (x.num.natAbs + x.den) * (y.num.natAbs + y.den) := by
    have hexp : (x.num.natAbs + x.den) * (y.num.natAbs + y.den) = x.num.natAbs * y.num.natAbs +
        x.num.natAbs * y.den + y.num.natAbs * x.den + x.den * y.den := by ring
    omega
  omega

/-- The same for a finite sum (not in the paper, as `add_numDen_le`). -/
lemma sum_numDen_le {ι : Type*} (s : Finset ι) (x : ι → ℚ) :
    (∑ i ∈ s, x i).num.natAbs + (∑ i ∈ s, x i).den ≤ ∏ i ∈ s, ((x i).num.natAbs + (x i).den) ∧
    (∑ i ∈ s, x i).den ≤ ∏ i ∈ s, (x i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj, prod_insert hj]
    obtain ⟨h1, h2⟩ := add_numDen_le (x j) (∑ i ∈ s, x i)
    exact ⟨h1.trans (Nat.mul_le_mul_left _ ih.1), h2.trans (Nat.mul_le_mul_left _ ih.2)⟩

/-- A finite sum has encoding length at most `2 + ∑_i w(x_i)`, by writing the terms over the
product of their denominators (not in the paper: the rule for sums, for any number of terms). -/
theorem enc_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℚ) :
    enc (∑ i ∈ s, x i) ≤ 2 + ∑ i ∈ s, wt (x i) := by
  obtain ⟨h1, h2⟩ := sum_numDen_le s x
  refine (enc_le_of_le _ h1 h2).trans ?_
  have c1 := clog_prod_le s fun i => (x i).num.natAbs + (x i).den
  have c2 := clog_prod_le s fun i => (x i).den
  simp only [wt, sum_add_distrib]
  omega

/-- "…, and a sum at most twice the sum of their encoding lengths, as one sees by writing the terms
over the product of their denominators." (the proof of `lem:exactbr`, line 1810), for a nonempty
finite sum. -/
theorem enc_sum_le_two_mul {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (x : ι → ℚ) :
    enc (∑ i ∈ s, x i) ≤ 2 * ∑ i ∈ s, enc (x i) := by
  refine (enc_sum_le s x).trans ?_
  have h : ∑ i ∈ s, (wt (x i) + 2) ≤ ∑ i ∈ s, 2 * enc (x i) :=
    sum_le_sum fun i _ => wt_add_two_le (x i)
  rw [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum] at h
  have := hs.card_pos
  omega

/-- The rule for sums for two terms: `⟨x + y⟩ ≤ 2(⟨x⟩ + ⟨y⟩)` (the proof of `lem:exactbr`, line
1810). -/
theorem enc_add (x y : ℚ) : enc (x + y) ≤ 2 * (enc x + enc y) := by
  obtain ⟨h1, h2⟩ := add_numDen_le x y
  refine (enc_le_of_le _ h1 h2).trans ?_
  have c1 := clog_mul_le (x.num.natAbs + x.den) (y.num.natAbs + y.den)
  have c2 := clog_mul_le x.den y.den
  have w1 := wt_add_two_le x
  have w2 := wt_add_two_le y
  unfold wt at w1 w2
  omega

/-- The rule for differences of two terms (not in the paper, by `enc_neg`). -/
theorem enc_sub (x y : ℚ) : enc (x - y) ≤ 2 * (enc x + enc y) := by
  rw [sub_eq_add_neg, ← enc_neg y]
  exact enc_add x (-y)

/-- The rule for sums of three terms: `⟨x + y + z⟩ ≤ 2(⟨x⟩ + ⟨y⟩ + ⟨z⟩)` (the proof of
`lem:exactbr`, line 1835: "a sum of three terms"). -/
theorem enc_add₃ (x y z : ℚ) : enc (x + y + z) ≤ 2 * (enc x + enc y + enc z) := by
  have h := enc_sum_le_two_mul (s := (univ : Finset (Fin 3))) univ_nonempty ![x, y, z]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact h

/-- The encoding length of a sum of two finite sums, written over the product of all the
denominators: at most `2` plus the weights of the terms (not in the paper). -/
lemma enc_add_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → ℚ) (y : κ → ℚ) :
    enc (∑ i ∈ s, x i + ∑ j ∈ t, y j) ≤ 2 + ∑ i ∈ s, wt (x i) + ∑ j ∈ t, wt (y j) := by
  obtain ⟨hA1, hA2⟩ := sum_numDen_le s x
  obtain ⟨hW1, hW2⟩ := sum_numDen_le t y
  obtain ⟨h1, h2⟩ := add_numDen_le (∑ i ∈ s, x i) (∑ j ∈ t, y j)
  refine (enc_le_of_le _ (h1.trans (Nat.mul_le_mul hA1 hW1))
    (h2.trans (Nat.mul_le_mul hA2 hW2))).trans ?_
  have c1 := clog_mul_le (∏ i ∈ s, ((x i).num.natAbs + (x i).den))
    (∏ j ∈ t, ((y j).num.natAbs + (y j).den))
  have c2 := clog_mul_le (∏ i ∈ s, (x i).den) (∏ j ∈ t, (y j).den)
  have p1 := clog_prod_le s fun i => (x i).num.natAbs + (x i).den
  have p2 := clog_prod_le t fun j => (y j).num.natAbs + (y j).den
  have p3 := clog_prod_le s fun i => (x i).den
  have p4 := clog_prod_le t fun j => (y j).den
  simp only [wt, sum_add_distrib]
  omega

/-- `∑_i w(x_i) ≤ 2 ∑_i ⟨x_i⟩` (not in the paper). -/
lemma sum_wt_le {ι : Type*} (s : Finset ι) (x : ι → ℚ) :
    ∑ i ∈ s, wt (x i) ≤ 2 * ∑ i ∈ s, enc (x i) := by
  rw [mul_sum]
  exact sum_le_sum fun i _ => by have := wt_add_two_le (x i); omega

/-! ### From explicit bounds to encoding lengths -/

/-- A number with magnitude and a denominator at most `2^B` (`Bits B`) is a rational of encoding
length at most `3B + 3` (not in the paper: "A rational number has `O(k + log μ^in_k)` bits if its
magnitude and its denominator are at most `2^{O(k+log μ^in_k)}`", the first sentence of the proof
of `lem:sizes`, with the encoding length of `lem:exactbr`). -/
theorem exists_rat_of_bits {B : ℕ} {x : ℝ} (h : Bits B x) :
    ∃ q : ℚ, (q : ℝ) = x ∧ enc q ≤ 3 * B + 3 := by
  obtain ⟨hx, n, hn, hnB, z, hz⟩ := h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨z / n, ?_, ?_⟩
  · push_cast
    rw [← hz]
    field_simp
  · refine (enc_le_of_eq_div hn rfl).trans ?_
    -- `|z| = n|x| ≤ 2^{2B}` and `n ≤ 2^B`
    have hzB : (z.natAbs : ℝ) ≤ 2 ^ (2 * B) := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← hz, abs_mul, abs_of_pos hn0, two_mul, pow_add]
      exact mul_le_mul hnB hx (abs_nonneg _) (by positivity)
    have hzB' : z.natAbs ≤ 2 ^ (2 * B) := by exact_mod_cast hzB
    have hnB' : n ≤ 2 ^ B := by exact_mod_cast hnB
    have c1 := (Nat.clog_mono_right 2 (Nat.add_le_add_right hzB' 1)).trans
      (clog_two_pow_add_one_le (2 * B))
    have c2 := (Nat.clog_mono_right 2 (Nat.add_le_add_right hnB' 1)).trans
      (clog_two_pow_add_one_le B)
    omega

/-! ### Instances of `𝒞_cut` with rational data -/

/-- An encoded instance (`def:cutform`: "encoded by the cut form, `m` and `β` in binary"), by its
data: a finite set `D` of arcs `(u, v)` on `E`, rational capacities `cap` on them and rational
weights `ω` (the cut form), and rational rewards `m` and curvatures `β`. That the data is a cut
form, a loopless digraph with nonnegative capacities, is `RatInst.IsCutForm`; that the encoded
instance lies in `𝒞_cut` is `RatInst.InCcut`; `RatInst.inCcut_iff` checks both. -/
structure RatInst (E : Type*) where
  /-- the arcs of the digraph -/
  D : Finset (E × E)
  /-- the capacities -/
  cap : E × E → ℚ
  /-- the weights -/
  ω : E → ℚ
  /-- the rewards -/
  m : E → ℚ
  /-- the curvatures -/
  β : E → ℚ

namespace RatInst

variable {E : Type*} (I : RatInst E)

/-- The data `(D, cap, ω)` of `I` is a cut form (`def:cutform`: "a loopless digraph `D` on `E`,
capacities `cap : D → ℚ_{≥0}` and weights `ω ∈ ℚ^E`"): `D` has no loops, and the capacities of its
arcs are nonnegative. -/
def IsCutForm : Prop := (∀ a ∈ I.D, a.1 ≠ a.2) ∧ ∀ a ∈ I.D, 0 ≤ I.cap a

/-- The cut form `(D, cap, ω)` of `I` over the reals, for data that is a cut form. -/
def form (h : I.IsCutForm) : CutForm E where
  D := I.D
  loopless := h.1
  cap a := I.cap a
  cap_nonneg a ha := by exact_mod_cast h.2 a ha
  ω e := I.ω e

/-- The rewards of `I` as real numbers. -/
def mR (e : E) : ℝ := I.m e

/-- The curvatures of `I` as real numbers. -/
def βR (e : E) : ℝ := I.β e

variable [Fintype E] [DecidableEq E]

/-- The function `f = cut_D + ω` of the data of `I` (`eq:cutform`), over the reals:
`f(S) = ∑_{(u, v) ∈ D : u ∈ S, v ∉ S} cap(u, v) + ω(S)`. For data that is a cut form, it is the
function of `I.form` (by definition). -/
def f (S : Finset E) : ℝ :=
  ∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, (I.cap a : ℝ) + ∑ e ∈ S, (I.ω e : ℝ)

/-- `⟨I⟩`, "the sum of the encoding lengths of the capacities, weights, rewards and curvatures of
`I`" (`stoc-sections/appD-hardness.tex:1796`). -/
def encI : ℕ :=
  ∑ a ∈ I.D, enc (I.cap a) + ∑ e, enc (I.ω e) + ∑ e, enc (I.m e) + ∑ e, enc (I.β e)

/-- `f(S) = cut_D(S) + ω(S)` computed in `ℚ`. -/
def fQ (S : Finset E) : ℚ := ∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, I.cap a + ∑ e ∈ S, I.ω e

/-- `t(S) = ∑_{e∈S} m_e/β_e` in `ℚ`. -/
def tQ (S : Finset E) : ℚ := ∑ e ∈ S, I.m e / I.β e

/-- `β⁻¹(S) = ∑_{e∈S} 1/β_e` in `ℚ`. -/
def binvQ (S : Finset E) : ℚ := ∑ e ∈ S, 1 / I.β e

omit [Fintype E] in
lemma fQ_cast (S : Finset E) : (I.fQ S : ℝ) = I.f S := by
  show ((∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, I.cap a + ∑ e ∈ S, I.ω e : ℚ) : ℝ) =
    ∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, (I.cap a : ℝ) + ∑ e ∈ S, (I.ω e : ℝ)
  push_cast
  rfl

omit [Fintype E] [DecidableEq E] in
lemma tQ_cast (S : Finset E) : (I.tQ S : ℝ) = ∑ e ∈ S, I.mR e / I.βR e := by
  show ((∑ e ∈ S, I.m e / I.β e : ℚ) : ℝ) = ∑ e ∈ S, (I.m e : ℝ) / (I.β e : ℝ)
  push_cast
  rfl

omit [Fintype E] [DecidableEq E] in
lemma binvQ_cast (S : Finset E) : (I.binvQ S : ℝ) = ∑ e ∈ S, 1 / I.βR e := by
  show ((∑ e ∈ S, 1 / I.β e : ℚ) : ℝ) = ∑ e ∈ S, 1 / (I.β e : ℝ)
  push_cast
  rfl

omit [DecidableEq E] in
/-- "Moreover, `n ≤ ⟨I⟩`, as every reward has encoding length at least `1`" (the proof of
membership in NP, `stoc-sections/appD-hardness.tex:1901`). -/
lemma card_le_encI : Fintype.card E ≤ I.encI := by
  have h : ∑ e : E, 1 ≤ ∑ e, enc (I.m e) := sum_le_sum fun e _ => by
    have := two_le_enc (I.m e)
    omega
  rw [sum_const, card_univ, smul_eq_mul, mul_one] at h
  unfold encI
  omega

omit [DecidableEq E] in
/-- The encoding length of a weight, reward or curvature is at most `⟨I⟩` (not in the paper; this
lemma and the next two). -/
lemma enc_ω_le (e : E) : enc (I.ω e) ≤ I.encI := by
  have := single_le_sum (f := fun e => enc (I.ω e)) (fun _ _ => Nat.zero_le _) (mem_univ e)
  unfold encI
  omega

omit [DecidableEq E] in
lemma enc_m_le (e : E) : enc (I.m e) ≤ I.encI := by
  have := single_le_sum (f := fun e => enc (I.m e)) (fun _ _ => Nat.zero_le _) (mem_univ e)
  unfold encI
  omega

omit [DecidableEq E] in
lemma enc_β_le (e : E) : enc (I.β e) ≤ I.encI := by
  have := single_le_sum (f := fun e => enc (I.β e)) (fun _ _ => Nat.zero_le _) (mem_univ e)
  unfold encI
  omega

omit [DecidableEq E] in
/-- `⟨t_e⟩ = ⟨m_e/β_e⟩ ≤ ⟨I⟩` (not in the paper: the proof of `lem:exactbr`(a) uses
`⟨t_e⟩ ≤ ⟨I⟩`). -/
lemma enc_t_le (e : E) : enc (I.m e / I.β e) ≤ I.encI := by
  have := enc_div (I.m e) (I.β e)
  have h1 := single_le_sum (f := fun e => enc (I.m e)) (fun _ _ => Nat.zero_le _) (mem_univ e)
  have h2 := single_le_sum (f := fun e => enc (I.β e)) (fun _ _ => Nat.zero_le _) (mem_univ e)
  unfold encI
  omega

omit [DecidableEq E] in
/-- The sum of the encoding lengths of the rewards is at least `2` for `E ≠ ∅` (not in the
paper). -/
lemma two_le_sum_enc [Nonempty E] (y : E → ℚ) : 2 ≤ ∑ e, enc (y e) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  exact (two_le_enc (y e)).trans
    (single_le_sum (f := fun e => enc (y e)) (fun _ _ => Nat.zero_le _) (mem_univ e))

/-- "Every value `f(S) = cut_D(S) + ω(S)` is a sum of distinct capacities and weights, … so all
three have encoding length at most `2⟨I⟩`" (the proof of `lem:exactbr`,
`stoc-sections/appD-hardness.tex:1812`), here for `f(S)`, for `E ≠ ∅` (§2 assumes a nonempty ground
set). -/
theorem enc_fQ_le [Nonempty E] (S : Finset E) : enc (I.fQ S) ≤ 2 * I.encI := by
  have h := enc_add_sum_le (I.D.filter fun a => a.1 ∈ S ∧ a.2 ∉ S) S I.cap I.ω
  -- the weights of the terms, summed over all arcs and all elements
  have s1 : ∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, wt (I.cap a) ≤ ∑ a ∈ I.D, wt (I.cap a) :=
    sum_le_sum_of_subset (filter_subset _ _)
  have s2 : ∑ e ∈ S, wt (I.ω e) ≤ ∑ e, wt (I.ω e) := sum_le_sum_of_subset (subset_univ _)
  have t1 := sum_wt_le I.D I.cap
  have t2 := sum_wt_le (univ : Finset E) I.ω
  have hm := two_le_sum_enc (E := E) I.m
  unfold fQ encI
  omega

omit [DecidableEq E] in
/-- "… and `t(S)` and `β⁻¹(S)` are sums of distinct quotients `m_e/β_e` and `1/β_e`, so all three
have encoding length at most `2⟨I⟩`" (the proof of `lem:exactbr`, line 1812), here for `t(S)`, for
`E ≠ ∅`. -/
theorem enc_tQ_le [Nonempty E] (S : Finset E) : enc (I.tQ S) ≤ 2 * I.encI := by
  have h := enc_sum_le S fun e => I.m e / I.β e
  have s1 : ∑ e ∈ S, wt (I.m e / I.β e) ≤ ∑ e, wt (I.m e / I.β e) :=
    sum_le_sum_of_subset (subset_univ _)
  have t1 : ∑ e, wt (I.m e / I.β e) ≤ 2 * ∑ e, (enc (I.m e) + enc (I.β e)) := by
    rw [mul_sum]
    exact sum_le_sum fun e _ => by
      have := wt_add_two_le (I.m e / I.β e)
      have := enc_div (I.m e) (I.β e)
      omega
  rw [sum_add_distrib] at t1
  have hω := two_le_sum_enc (E := E) I.ω
  unfold tQ encI
  omega

omit [DecidableEq E] in
/-- "… and `t(S)` and `β⁻¹(S)` are sums of distinct quotients `m_e/β_e` and `1/β_e`, so all three
have encoding length at most `2⟨I⟩`" (the proof of `lem:exactbr`, line 1812), here for `β⁻¹(S)`,
for `E ≠ ∅`. -/
theorem enc_binvQ_le [Nonempty E] (S : Finset E) : enc (I.binvQ S) ≤ 2 * I.encI := by
  have h := enc_sum_le S fun e => 1 / I.β e
  have s1 : ∑ e ∈ S, wt (1 / I.β e) ≤ ∑ e, wt (1 / I.β e) := sum_le_sum_of_subset (subset_univ _)
  have t1 : ∑ e, wt (1 / I.β e) ≤ 2 * ∑ e, enc (I.β e) := by
    rw [mul_sum]
    exact sum_le_sum fun e _ => by
      have := wt_add_two_le (1 / I.β e)
      rw [one_div, enc_inv] at this
      rw [one_div]
      omega
  have hω := two_le_sum_enc (E := E) I.ω
  unfold binvQ encI
  omega

/-- The encoded instance `I` lies in `𝒞_cut` (`def:cutform`): its data is a cut form
(`IsCutForm`), and `(f, m, β)` lies in `𝒞_cut` (`Ccut`: `m, β > 0`, and `f` is a polymatroid rank
function given by a cut form). -/
def InCcut : Prop := I.IsCutForm ∧ Ccut I.f I.mR I.βR

/-- `lem:cutforms`(b) for the data of `I` (`stoc-sections/appD-hardness.tex:109`, the check at lines
140-141): the encoded instance `I` lies in `𝒞_cut` if and only if `D` has no loops, all capacities
are nonnegative, `m` and `β` are positive, and every weight `ω_e` is at least the total capacity
of the arcs of `D` that enter `e`. These are `|D|` tests of the end points of arcs and
`|D| + 3|E|` comparisons of rationals ("In particular, membership in `𝒞_cut` is decided in
polynomial time"); the additions and comparisons are not counted.

The proof's steps, the checks of the paper's sentence in its order: (5a) "that `D` has no loops,
that all capacities are nonnegative", so that the data is the cut form `I.form` with the function
`f`; (5b) "and that `m` and `β` are positive"; (5c) "and to compare, for each `e ∈ E`, the weight
`ω_e` with the sum of the capacities of the arcs entering `e`", which decides by `lem:cutforms`(b)
(`cutforms_b`) whether `f` is a polymatroid rank function. -/
theorem inCcut_iff :
    I.InCcut ↔ (∀ a ∈ I.D, a.1 ≠ a.2) ∧ (∀ a ∈ I.D, 0 ≤ I.cap a) ∧ (∀ e, 0 < I.m e) ∧
      (∀ e, 0 < I.β e) ∧ ∀ e, ∑ a ∈ I.D with a.2 = e, I.cap a ≤ I.ω e := by
  -- (5) "To decide whether an encoded instance `(f, m, β)` lies in `𝒞_cut`, it therefore suffices
  -- to check that `D` has no loops, that all capacities are nonnegative and that `m` and `β` are
  -- positive, and to compare, for each `e ∈ E`, the weight `ω_e` with the sum of the capacities of
  -- the arcs entering `e`. These are polynomially many additions and comparisons of input
  -- numbers."
  -- The Lean: the checks in this order; the additions and comparisons are not counted.
  -- (5a) "that `D` has no loops, that all capacities are nonnegative": the data is a cut form,
  -- `I.form`, whose function is `f`
  unfold InCcut IsCutForm
  refine and_assoc.trans (and_congr_right fun hl => and_congr_right fun hc => ?_)
  -- (5b) "and that `m` and `β` are positive"
  have hm : (∀ e, 0 < I.mR e) ↔ ∀ e, 0 < I.m e := forall_congr' fun e => Rat.cast_pos
  have hβ : (∀ e, 0 < I.βR e) ↔ ∀ e, 0 < I.β e := forall_congr' fun e => Rat.cast_pos
  -- (5c) "and to compare, for each `e ∈ E`, the weight `ω_e` with the sum of the capacities of the
  -- arcs entering `e`": by `lem:cutforms`(b), `f` is a polymatroid rank function if and only if
  -- these comparisons hold
  have hω : IsRankFunction I.f ↔ ∀ e, ∑ a ∈ I.D with a.2 = e, I.cap a ≤ I.ω e := by
    rw [show I.f = (I.form ⟨hl, hc⟩).fn from rfl, cutforms_b]
    refine forall_congr' fun e => ?_
    simp only [form]
    constructor <;> intro h <;> exact_mod_cast h
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    exact ⟨hm.1 h1, hβ.1 h2, hω.1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hm.2 h1, hβ.2 h2, hω.2 h3, ⟨I.form ⟨hl, hc⟩, fun S => rfl⟩⟩

instance : Decidable I.InCcut := decidable_of_iff _ I.inCcut_iff.symm

end RatInst

/-- A real instance whose numbers all have `Bits B` (the capacities on the arcs and the weights of a
cut form, the rewards and the curvatures) is given by rational data, a `RatInst` whose data is a
cut form, with `⟨I⟩ ≤ (|D| + 3|E|)(3B + 3)` (not in the paper: the bridge from the explicit bounds
of `lem:sizes` and the proof of `thm:gadget` to the encoding lengths of `lem:exactbr`). -/
theorem exists_ratInst_of_bits {E : Type*} [Fintype E] [DecidableEq E] (F : CutForm E)
    (m β : E → ℝ) {B : ℕ} (hcap : ∀ a ∈ F.D, Bits B (F.cap a)) (hω : ∀ e, Bits B (F.ω e))
    (hm : ∀ e, Bits B (m e)) (hβ : ∀ e, Bits B (β e)) :
    ∃ I : RatInst E, I.IsCutForm ∧ I.D = F.D ∧ (∀ S, I.f S = F.fn S) ∧ I.mR = m ∧ I.βR = β ∧
      I.encI ≤ (F.D.card + 3 * Fintype.card E) * (3 * B + 3) := by
  classical
  choose qω hqω hqω' using fun e => exists_rat_of_bits (hω e)
  choose qm hqm hqm' using fun e => exists_rat_of_bits (hm e)
  choose qβ hqβ hqβ' using fun e => exists_rat_of_bits (hβ e)
  have hcap' : ∀ a, ∃ q : ℚ, (a ∈ F.D → (q : ℝ) = F.cap a ∧ enc q ≤ 3 * B + 3) := fun a => by
    by_cases ha : a ∈ F.D
    · obtain ⟨q, h1, h2⟩ := exists_rat_of_bits (hcap a ha)
      exact ⟨q, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose qc hqc using hcap'
  let I : RatInst E :=
    { D := F.D
      cap := qc
      ω := qω
      m := qm
      β := qβ }
  -- the data of `I` is a cut form, as `F` is one
  have hI : I.IsCutForm := by
    refine ⟨F.loopless, fun a ha => ?_⟩
    have h := F.cap_nonneg a ha
    rw [← ((hqc a) ha).1] at h
    exact_mod_cast h
  refine ⟨I, hI, rfl, fun S => ?_, funext hqm, funext hqβ, ?_⟩
  · simp only [RatInst.f, CutForm.fn, CutForm.cut, I, hqω]
    congr 1
    exact sum_congr rfl fun a ha => ((hqc a) (mem_filter.1 ha).1).1
  · have h1 : ∑ a ∈ F.D, enc (qc a) ≤ ∑ a ∈ F.D, (3 * B + 3) :=
      sum_le_sum fun a ha => ((hqc a) ha).2
    have h2 : ∑ e, enc (qω e) ≤ ∑ e : E, (3 * B + 3) := sum_le_sum fun e _ => hqω' e
    have h3 : ∑ e, enc (qm e) ≤ ∑ e : E, (3 * B + 3) := sum_le_sum fun e _ => hqm' e
    have h4 : ∑ e, enc (qβ e) ≤ ∑ e : E, (3 * B + 3) := sum_le_sum fun e _ => hqβ' e
    simp only [sum_const, card_univ, smul_eq_mul] at h1 h2 h3 h4
    show ∑ a ∈ F.D, enc (qc a) + ∑ e, enc (qω e) + ∑ e, enc (qm e) + ∑ e, enc (qβ e) ≤ _
    nlinarith

end

end Hardness

end Stoc
