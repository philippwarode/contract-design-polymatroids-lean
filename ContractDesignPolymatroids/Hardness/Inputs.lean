-- stamp r9 2026-11-03
import ContractDesignPolymatroids.Hardness.Tower

/-!
# The inputs: `def:family` and `lem:inputs`

The STOC version's `def:family` (Appendix C.3, `sec:D-correct`,
`stoc-sections/appD-hardness.tex:183-185`) and `lem:inputs` (Appendix C.7, `sec:D-alllevels`,
"Every level works", lines 1176-1214), for the levels of `def:tower` (`μT`, `R1T`, `ΓT` of
`ContractDesignPolymatroids/Hardness/Tower.lean`):

* `InF`: the family `𝔉` of `def:family`;
* `lenR`, `μhat`, `ℓhat`: `|𝓡_j| = R_1^{(j)} − R_0`, `μ̂_j = μ_j/μ_{j+1}` and
  `ℓ̂_j = |𝓡_j|/μ_{j+1}`;
* `inputs`: `lem:inputs`, with the added step `subsetSum_injOn` (a sequence in which every entry
  exceeds the sum of the earlier ones has distinct subset sums, which the paper uses without
  proof).

The text after `def:family` (line 187: in every `μ ∈ 𝔉`, each entry exceeds the sum of the earlier
ones, so the `2^k` numbers `μ^⊤χ` are distinct) is not a result and has no declaration of its own;
for the `μ_j` of the levels, the property is the third conjunct of `inputs`.

Indices of the input from `0`: `μin i` is the STOC version's `μ^in_{i+1}`.

Taken over on 2026-10-20 from `Paper/Hardness/Inputs.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-- **`def:family`** (Definition C.5, `stoc-sections/appD-hardness.tex:183-185`): `𝔉` is the set of
all `μ ∈ ℤ^k_{>0}`, `k ≥ 1`, for which there is an integer `H ≥ 1` with
`H 8^{i−1} ≤ μ_i < (11/10) H 8^{i−1}` for `i ∈ [k]`. Here `μ : ℕ → ℕ` has indices from `0` (`μ i`
is `μ_{i+1}`, and the entries `μ i` with `i ≥ k` are not used), so the condition reads
`H 8^i ≤ μ i < (11/10) H 8^i` for `i < k`. -/
def InF (μ : ℕ → ℕ) (k : ℕ) : Prop :=
  1 ≤ k ∧ (∀ i < k, 0 < μ i) ∧
    ∃ H : ℕ, 1 ≤ H ∧ ∀ i < k, (H : ℝ) * 8 ^ i ≤ μ i ∧ (μ i : ℝ) < 11 / 10 * H * 8 ^ i

section Inputs

variable (μin : ℕ → ℕ)

/-- `|𝓡_j| = R_1^{(j)} − R_0`, the length of `𝓡_j` (before `lem:inputs`). -/
def lenR (j : ℕ) : ℝ := R1T μin j - R0

/-- `μ̂_j = μ_j/μ_{j+1}` (`lem:inputs`). -/
def μhat (j : ℕ) : ℝ := μT μin j / μT μin (j + 1)

/-- `ℓ̂_j = |𝓡_j|/μ_{j+1}` (`lem:inputs`). -/
def ℓhat (j : ℕ) : ℝ := lenR μin j / μT μin (j + 1)

variable {μin}

/-- `|𝓡_j| = ∑_{i ≤ j} μ_i + 1/15` (the proof of `lem:inputs`). -/
lemma lenR_eq (j : ℕ) : lenR μin j = ∑ i ∈ range (j + 1), μT μin i + 1 / 15 := by
  unfold lenR R1T R0
  ring

/-- A sequence of positive numbers in which every entry exceeds the sum of the earlier ones has
distinct subset sums (not in the paper: the proof of `lem:inputs` uses it without proof): if
`μ_0, …, μ_n > 0` and `μ_{j+1} > ∑_{i ≤ j} μ_i` for `j < n`, then `Q ↦ ∑_{i ∈ Q} μ_i` is injective
on the subsets of `{0, …, n}`; by induction on `n`, as a set that contains `n + 1` has a larger
sum than every set that does not. -/
lemma subsetSum_injOn {μs : ℕ → ℝ} : ∀ n : ℕ, (∀ i ≤ n, 0 < μs i) →
    (∀ j < n, ∑ i ∈ range (j + 1), μs i < μs (j + 1)) →
      Set.InjOn (fun Q => ∑ i ∈ Q, μs i) ((range (n + 1)).powerset : Set (Finset ℕ)) := by
  intro n
  induction n with
  | zero =>
    intro hp _ Q hQ Q' hQ' hs
    have hr : range (0 + 1) = {0} := rfl
    rw [mem_coe, mem_powerset, hr] at hQ hQ'
    have h0 := hp 0 le_rfl
    simp only at hs
    rcases subset_singleton_iff.1 hQ with rfl | rfl <;>
      rcases subset_singleton_iff.1 hQ' with rfl | rfl
    · rfl
    · simp at hs; linarith
    · simp at hs; linarith
    · rfl
  | succ n ih =>
    intro hp hs Q hQ Q' hQ' hsum
    rw [mem_coe, mem_powerset] at hQ hQ'
    simp only at hsum
    have hs' : ∀ j < n, ∑ i ∈ range (j + 1), μs i < μs (j + 1) := fun j hj => hs j (by omega)
    have hp' : ∀ i ≤ n, 0 < μs i := fun i hi => hp i (by omega)
    have hsub : ∀ {P : Finset ℕ}, P ⊆ range (n + 1 + 1) → P.erase (n + 1) ⊆ range (n + 1) :=
      fun hP i hi => by
        have h1 := mem_range.1 (hP (mem_of_mem_erase hi))
        have h2 := ne_of_mem_erase hi
        exact mem_range.2 (by omega)
    -- a set without the top element sums to less than the top element
    have hlow : ∀ P ⊆ range (n + 1), ∑ i ∈ P, μs i < μs (n + 1) := fun P hP =>
      lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg hP fun i hi _ =>
        (hp i (by have := mem_range.1 hi; omega)).le) (hs n (by omega))
    have hnn : ∀ P ⊆ range (n + 1 + 1), 0 ≤ ∑ i ∈ P, μs i := fun P hP =>
      sum_nonneg fun i hi => (hp i (by have := mem_range.1 (hP hi); omega)).le
    by_cases h1 : n + 1 ∈ Q <;> by_cases h2 : n + 1 ∈ Q'
    · rw [← add_sum_erase Q _ h1, ← add_sum_erase Q' _ h2, add_right_inj] at hsum
      have := ih hp' hs' (mem_coe.2 (mem_powerset.2 (hsub hQ)))
        (mem_coe.2 (mem_powerset.2 (hsub hQ'))) hsum
      rw [← insert_erase h1, ← insert_erase h2, this]
    · rw [← add_sum_erase Q _ h1] at hsum
      have hQ'' : Q' ⊆ range (n + 1) := by rw [← erase_eq_of_notMem h2]; exact hsub hQ'
      have := hlow Q' hQ''
      have := hnn (Q.erase (n + 1)) ((erase_subset _ _).trans hQ)
      linarith
    · rw [← add_sum_erase Q' _ h2] at hsum
      have hQ'' : Q ⊆ range (n + 1) := by rw [← erase_eq_of_notMem h1]; exact hsub hQ
      have := hlow Q hQ''
      have := hnn (Q'.erase (n + 1)) ((erase_subset _ _).trans hQ')
      linarith
    · have e1 : Q ⊆ range (n + 1) := by rw [← erase_eq_of_notMem h1]; exact hsub hQ
      have e2 : Q' ⊆ range (n + 1) := by rw [← erase_eq_of_notMem h2]; exact hsub hQ'
      exact ih hp' hs' (mem_coe.2 (mem_powerset.2 e1)) (mem_coe.2 (mem_powerset.2 e2)) hsum

/-- **`lem:inputs`** (Lemma C.19, `stoc-sections/appD-hardness.tex:1178-1192`, proof lines
1194-1214): let `μ^in ∈ 𝔉` have length `k ≥ 2`. Then `μ_1 ∈ (80/33, 44/15)`, and for every `j ≥ 1`
for which `μ_{j+1}` is defined (`j + 1 < k`), `μ̂_j ∈ (5/44, 11/80)`, `ℓ̂_j < 253/1600` and
`1/μ_{j+1} < 33/640`. Moreover, `μ_{j+1} > ∑_{i ≤ j} μ_i` and `|𝓡_j| < μ_{j+1}` for every `j ≥ 0`
for which `μ_{j+1}` is defined. So `Γ_j` has `2^{j+1}` points for every `j` for which `μ_j` is
defined (`j < k`), and for every `j` for which `μ_{j+1}` is defined, the transition
`[R_1^{(j)}, R_0 + μ_{j+1}]` has positive length.

The proof's steps: (1) with `H` as in `def:family`, the ratio of two consecutive inputs lies in
`(80/11, 44/5)`, which gives the ranges of `μ_1 = μ^in_2/(3μ^in_1)` and of
`μ̂_j = μ^in_{j+1}/μ^in_{j+2}`; (2) `1/μ_{j+1} = 3μ^in_1/μ^in_{j+2} < (33/10)·8^{−j−1} ≤ 33/640`
for `j ≥ 1`; (3) `|𝓡_j| = ∑_{i ≤ j} μ_i + 1/15` and `μ_i = μ^in_{i+1}/(3μ^in_1)`, so
`|𝓡_j|/μ_{j+1} = (∑_{i=1}^{j+1} μ^in_i + μ^in_1/5)/μ^in_{j+2}`; (4) for `j ≥ 1`, the numerator is
less than `(11/10)H((8^{j+1} − 1)/7 + 1/5)` and the denominator at least `H8^{j+1}`, so
`ℓ̂_j < (11/10)(1/7 + (2/35)·8^{−j−1}) ≤ (11/10)(1/7 + (2/35)·8^{−2}) = 253/1600`; (5) for
`j = 0`, `|𝓡_0|/μ_1 = 2/(5μ_1) < 33/200`; (6) so `|𝓡_j|/μ_{j+1} < 1` for every `j ≥ 0`, that is,
`∑_{i ≤ j} μ_i < |𝓡_j| < μ_{j+1}`, which gives the remaining claims, as a sequence in which every
entry exceeds the sum of the earlier ones has distinct subset sums (`subsetSum_injOn`). -/
theorem inputs {k : ℕ} (hF : InF μin k) (hk : 2 ≤ k) :
    μT μin 1 ∈ Set.Ioo (80 / 33) (44 / 15) ∧
    (∀ j, 1 ≤ j → j + 1 < k →
      μhat μin j ∈ Set.Ioo (5 / 44) (11 / 80) ∧ ℓhat μin j < 253 / 1600 ∧
        1 / μT μin (j + 1) < 33 / 640) ∧
    (∀ j, j + 1 < k → ∑ i ∈ range (j + 1), μT μin i < μT μin (j + 1) ∧
      lenR μin j < μT μin (j + 1)) ∧
    (∀ j, j < k → (ΓT μin j).card = 2 ^ (j + 1)) ∧
    (∀ j, j + 1 < k → R1T μin j < R0 + μT μin (j + 1)) := by
  obtain ⟨-, hpos, H, hH, hb⟩ := hF
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hμ0 : (0 : ℝ) < μin 0 := by exact_mod_cast hpos 0 (by omega)
  have hd : ∀ j, j + 1 < k → (0 : ℝ) < μin (j + 1) := fun j hj => by
    exact_mod_cast hpos (j + 1) hj
  have hμT : ∀ i, μT μin i = μin i / (3 * μin 0) := fun i => by
    unfold μT δT
    ring
  have h3 : (0 : ℝ) < 3 * μin 0 := by positivity
  -- (1) "With `H` as in the definition of `𝔉`, `μ^in_i ∈ [H8^{i−1}, (11/10)H8^{i−1})`, so the ratio
  -- of two consecutive inputs lies in `(80/11, 44/5)`. This gives the ranges of
  -- `μ_1 = μ^in_2/(3μ^in_1)` and of `μ̂_j = μ^in_{j+1}/μ^in_{j+2}`."
  have hratio : ∀ i, i + 1 < k → 80 / 11 * (μin i : ℝ) < μin (i + 1) ∧
      (μin (i + 1) : ℝ) < 44 / 5 * μin i := by
    intro i hi
    obtain ⟨a1, a2⟩ := hb i (by omega)
    obtain ⟨b1, b2⟩ := hb (i + 1) hi
    have e : (8 : ℝ) ^ (i + 1) = 8 * 8 ^ i := by ring
    rw [e] at b1 b2
    have : (0 : ℝ) < H * 8 ^ i := by positivity
    constructor <;> nlinarith
  have hμ1 : μT μin 1 ∈ Set.Ioo (80 / 33) (44 / 15) := by
    obtain ⟨r1, r2⟩ := hratio 0 (by omega)
    rw [hμT]
    constructor
    · rw [lt_div_iff₀ h3]
      linarith
    · rw [div_lt_iff₀ h3]
      linarith
  have hμhat : ∀ j, 1 ≤ j → j + 1 < k → μhat μin j ∈ Set.Ioo (5 / 44) (11 / 80) := by
    intro j _ hj
    obtain ⟨r1, r2⟩ := hratio j hj
    rw [μhat, hμT, hμT, div_div_div_cancel_right₀ h3.ne']
    constructor
    · rw [lt_div_iff₀ (hd j hj)]
      linarith
    · rw [div_lt_iff₀ (hd j hj)]
      linarith
  -- (2) "Also `1/μ_{j+1} = 3μ^in_1/μ^in_{j+2} < (33/10)·8^{−j−1} ≤ 33/640` for `j ≥ 1`."
  have h64 : ∀ j, 1 ≤ j → (64 : ℝ) ≤ 8 ^ (j + 1) := fun j hj1 => by
    calc (64 : ℝ) = 8 ^ 2 := by norm_num
      _ ≤ 8 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hinv : ∀ j, 1 ≤ j → j + 1 < k → 1 / μT μin (j + 1) < 33 / 640 := by
    intro j hj1 hj
    obtain ⟨d1, -⟩ := hb (j + 1) hj
    obtain ⟨-, a2⟩ := hb 0 (by omega)
    simp only [pow_zero, mul_one] at a2
    calc 1 / μT μin (j + 1) = 3 * μin 0 / μin (j + 1) := by rw [hμT, one_div_div]
      _ < 33 / 10 * (1 / 8 ^ (j + 1)) := by
        rw [mul_one_div, div_lt_div_iff₀ (hd j hj) (by positivity)]
        nlinarith [pow_pos (show (0 : ℝ) < 8 by norm_num) (j + 1)]
      _ ≤ 33 / 640 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [h64 j hj1]
  -- (3) "Next, `|𝓡_j| = ∑_{i ≤ j} μ_i + 1/15` and `μ_i = μ^in_{i+1}/(3μ^in_1)`, so
  -- `|𝓡_j|/μ_{j+1} = (∑_{i=1}^{j+1} μ^in_i + (1/5)μ^in_1)/μ^in_{j+2}`."
  have e3 : ∀ j, j + 1 < k →
      ℓhat μin j = (∑ i ∈ range (j + 1), (μin i : ℝ) + μin 0 / 5) / μin (j + 1) := by
    intro j hj
    have := hd j hj
    rw [ℓhat, lenR_eq, hμT]
    simp only [hμT, ← sum_div]
    field_simp
    ring
  -- (4) "For `j ≥ 1`, the numerator is less than `(11/10)H((1/7)(8^{j+1} − 1) + 1/5)` and the
  -- denominator is at least `H8^{j+1}`, so
  -- `ℓ̂_j < (11/10)(1/7 + (2/35)·8^{−j−1}) ≤ (11/10)(1/7 + (2/35)·8^{−2}) = 253/1600`."
  have hℓ : ∀ j, 1 ≤ j → j + 1 < k → ℓhat μin j < 253 / 1600 := by
    intro j hj1 hj
    obtain ⟨d1, -⟩ := hb (j + 1) hj
    have hnum : ∑ i ∈ range (j + 1), (μin i : ℝ) + μin 0 / 5 <
        11 / 10 * H * ((8 ^ (j + 1) - 1) / 7 + 1 / 5) := by
      have hgeom : ∑ i ∈ range (j + 1), (8 : ℝ) ^ i = (8 ^ (j + 1) - 1) / 7 := by
        rw [geom_sum_eq (by norm_num)]
        norm_num
      have hs : ∑ i ∈ range (j + 1), (μin i : ℝ) < 11 / 10 * H * ((8 ^ (j + 1) - 1) / 7) := by
        rw [← hgeom, mul_sum]
        exact sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun i hi =>
          (hb i (by have := mem_range.1 hi; omega)).2
      have h0 := (hb 0 (by omega)).2
      simp only [pow_zero, mul_one] at h0
      linarith
    have hnum0 : 0 < ∑ i ∈ range (j + 1), (μin i : ℝ) + μin 0 / 5 := by
      have : 0 ≤ ∑ i ∈ range (j + 1), (μin i : ℝ) := sum_nonneg fun i _ => Nat.cast_nonneg _
      linarith
    have hHne : (H : ℝ) ≠ 0 := hH0.ne'
    calc ℓhat μin j = (∑ i ∈ range (j + 1), (μin i : ℝ) + μin 0 / 5) / μin (j + 1) := e3 j hj
      _ ≤ (∑ i ∈ range (j + 1), (μin i : ℝ) + μin 0 / 5) / (H * 8 ^ (j + 1)) :=
        div_le_div_of_nonneg_left hnum0.le (by positivity) d1
      _ < 11 / 10 * H * ((8 ^ (j + 1) - 1) / 7 + 1 / 5) / (H * 8 ^ (j + 1)) :=
        div_lt_div_of_pos_right hnum (by positivity)
      _ = 11 / 10 * (1 / 7 + 2 / 35 * (1 / 8 ^ (j + 1))) := by
        field_simp
        ring
      _ ≤ 11 / 10 * (1 / 7 + 2 / 35 * (1 / 8 ^ 2)) := by
        have : (1 : ℝ) / 8 ^ (j + 1) ≤ 1 / 8 ^ 2 :=
          one_div_le_one_div_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num) (by omega))
        linarith
      _ = 253 / 1600 := by norm_num
  -- (5) "For `j = 0`, `|𝓡_0|/μ_1 = 2/(5μ_1) < 33/200`."
  have hR0 : lenR μin 0 = 2 / 5 := by
    rw [lenR_eq, sum_range_one, μT_zero (by exact_mod_cast hpos 0 (by omega))]
    norm_num
  have h5 : ℓhat μin 0 = 2 / (5 * μT μin 1) ∧ 2 / (5 * μT μin 1) < 33 / 200 := by
    refine ⟨by rw [ℓhat, hR0, div_div], ?_⟩
    rw [div_lt_div_iff₀ (by linarith [hμ1.1]) (by norm_num)]
    linarith [hμ1.1]
  -- (6) "So `|𝓡_j|/μ_{j+1} < 1` for every `j ≥ 0`, that is, `∑_{i ≤ j} μ_i < |𝓡_j| < μ_{j+1}`."
  have hlt1 : ∀ j, j + 1 < k → ℓhat μin j < 1 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [h5.1]
      linarith [h5.2]
    · linarith [hℓ j hj1 hj]
  have hmore : ∀ j, j + 1 < k → ∑ i ∈ range (j + 1), μT μin i < μT μin (j + 1) ∧
      lenR μin j < μT μin (j + 1) := by
    intro j hj
    have hμj : 0 < μT μin (j + 1) := by
      rw [hμT]
      have := hd j hj
      positivity
    have hlt : lenR μin j < μT μin (j + 1) := by
      have := hlt1 j hj
      rwa [ℓhat, div_lt_one hμj] at this
    refine ⟨?_, hlt⟩
    have := lenR_eq (μin := μin) j
    linarith
  -- (6) "This gives the remaining claims, as a sequence in which every entry exceeds the sum of
  -- the earlier ones has distinct subset sums."
  refine ⟨hμ1, fun j hj1 hj => ⟨hμhat j hj1 hj, hℓ j hj1 hj, hinv j hj1 hj⟩, hmore,
    fun j hj => ?_, fun j hj => ?_⟩
  · -- "`Γ_j` has `2^{j+1}` points" (`subsetSum_injOn`)
    rw [ΓT, card_image_of_injOn, card_powerset, card_range]
    intro Q hQ Q' hQ' h
    simp only [add_right_inj] at h
    refine subsetSum_injOn j (fun i hi => ?_) (fun l hl => (hmore l (by omega)).1) hQ hQ' h
    rw [hμT]
    have : (0 : ℝ) < μin i := by exact_mod_cast hpos i (by omega)
    positivity
  · -- "the transition `[R_1^{(j)}, R_0 + μ_{j+1}]` has positive length"
    have := (hmore j hj).2
    unfold lenR at this
    linarith

end Inputs

end

end Hardness

end Stoc
