-- stamp r4 2026-11-01
import Mathlib

/-!
# The distinct values of a vector and the layer-cake identity

The identity of the proof of `prop:optchar` (`stoc-sections/appB-quadratic.tex:13-30`): for the
distinct values `θ_1 > θ_2 > ⋯ > θ_k` of `ρ` above a level `c`, with `θ_{k+1} := c` and the level
sets `A_i := {e | ρ_e ≥ θ_i}`,
`∑_e (ρ_e − c) y_e = ∑_{i=1}^k (θ_i − θ_{i+1}) y(A_i)`.
The STOC version uses it with `c = 0` in the proof of `prop:optchar`, and with a level `c` below all
marginals in the proof of `lem:fullplane`(a) (`stoc-sections/appB-tools.tex`).

Indices from 0: `theta ρ c i` for `i < k` is the STOC version's `θ_{i+1}`, so
`theta ρ c 0 > theta ρ c 1 > ⋯ > theta ρ c (k − 1)`, and `theta ρ c i = c` for `i ≥ k` (the STOC
version's `θ_{k+1}`).

* `layerCake`: the identity.
* `levelSet_eq_theta`: every level set `{e | ρ_e ≥ t}` with `t > c` is one of the `A_i` or empty,
  the step "these are all nonempty positive level sets" of the proof of `prop:optchar`.
-/

namespace Stoc

open Finset

noncomputable section

variable {E : Type*} [Fintype E]

/-- The values of `ρ` above `c`. -/
def valsAbove (ρ : E → ℝ) (c : ℝ) : Finset ℝ :=
  (univ.image ρ).filter fun t => c < t

/-- Their number `k`. -/
def numVals (ρ : E → ℝ) (c : ℝ) : ℕ :=
  #(valsAbove ρ c)

/-- The distinct values of `ρ` above `c` in decreasing order: `theta ρ c i` is the `(i + 1)`-st
largest one for `i < k` (the STOC version's `θ_{i+1}`), and `theta ρ c i = c` for `i ≥ k` (its
`θ_{k+1} := c`). -/
def theta (ρ : E → ℝ) (c : ℝ) (i : ℕ) : ℝ :=
  if h : i < numVals ρ c then
    (valsAbove ρ c).orderEmbOfFin rfl ⟨numVals ρ c - 1 - i, by unfold numVals at h ⊢; omega⟩
  else c

variable {ρ : E → ℝ} {c : ℝ}

theorem numVals_eq : numVals ρ c = #(valsAbove ρ c) := rfl

theorem theta_mem {i : ℕ} (hi : i < numVals ρ c) : theta ρ c i ∈ valsAbove ρ c := by
  simp only [theta, hi, dite_true]
  exact orderEmbOfFin_mem _ _ _

theorem c_lt_theta {i : ℕ} (hi : i < numVals ρ c) : c < theta ρ c i :=
  (mem_filter.1 (theta_mem hi)).2

theorem theta_of_le {i : ℕ} (hi : numVals ρ c ≤ i) : theta ρ c i = c := by
  simp [theta, not_lt.2 hi]

/-- The values decrease strictly: `θ_1 > θ_2 > ⋯ > θ_k > θ_{k+1} = c`. -/
theorem theta_lt_theta {i j : ℕ} (hij : i < j) (hj : j ≤ numVals ρ c) :
    theta ρ c j < theta ρ c i := by
  have hi : i < numVals ρ c := by omega
  rcases hj.lt_or_eq with hj | rfl
  · simp only [theta, hi, hj, dite_true]
    exact (valsAbove ρ c).orderEmbOfFin rfl |>.strictMono (Fin.mk_lt_mk.2 (by omega))
  · rw [theta_of_le le_rfl]
    exact c_lt_theta hi

theorem theta_le_theta_iff {i j : ℕ} (hi : i < numVals ρ c) (hj : j < numVals ρ c) :
    theta ρ c i ≤ theta ρ c j ↔ j ≤ i := by
  constructor
  · intro h
    by_contra hji
    exact absurd h (not_le.2 (theta_lt_theta (not_le.1 hji) hj.le))
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact (theta_lt_theta h hi.le).le
    · exact le_rfl

/-- Every value of `ρ` above `c` is one of the `θ_i`. -/
theorem exists_theta_eq {e : E} (he : c < ρ e) : ∃ j < numVals ρ c, theta ρ c j = ρ e := by
  have hmem : ρ e ∈ valsAbove ρ c := mem_filter.2 ⟨mem_image_of_mem ρ (mem_univ e), he⟩
  have hrange := Set.ext_iff.1 ((valsAbove ρ c).range_orderEmbOfFin rfl) (ρ e)
  obtain ⟨⟨l, hl⟩, hle⟩ := hrange.2 (mem_coe.2 hmem)
  have hk := numVals_eq (ρ := ρ) (c := c)
  have hlt : numVals ρ c - 1 - l < numVals ρ c := by omega
  refine ⟨numVals ρ c - 1 - l, hlt, ?_⟩
  simp only [theta, hlt, dite_true]
  rw [← hle]
  congr 1
  ext
  simp only
  omega

/-- The telescoping sum `∑_{i=j}^{k} (θ_i − θ_{i+1}) = θ_j − θ_{k+1} = θ_j − c` (indices from 0). -/
theorem sum_Ico_theta_sub {j : ℕ} (hj : j ≤ numVals ρ c) :
    ∑ i ∈ Ico j (numVals ρ c), (theta ρ c i - theta ρ c (i + 1)) = theta ρ c j - c := by
  rw [sum_Ico_eq_sum_range]
  have h := sum_range_sub' (fun l => theta ρ c (j + l)) (numVals ρ c - j)
  simp only [← add_assoc, add_zero] at h
  rw [h, Nat.add_sub_cancel' hj, theta_of_le le_rfl]

/-- **The layer-cake identity** of the proof of `prop:optchar` (not in the paper: the STOC version
states it without proof, `stoc-sections/appB-quadratic.tex:24-25`): for `ρ ≥ c` and every `y`,
`∑_e (ρ_e − c) y_e = ∑_{i=1}^k (θ_i − θ_{i+1}) y(A_i)` with `A_i = {e | ρ_e ≥ θ_i}` and
`θ_{k+1} = c` (indices from 0). -/
theorem layerCake (hc : ∀ e, c ≤ ρ e) (y : E → ℝ) :
    ∑ e, (ρ e - c) * y e =
      ∑ i ∈ range (numVals ρ c),
        (theta ρ c i - theta ρ c (i + 1)) *
          ∑ e ∈ univ.filter (fun e => theta ρ c i ≤ ρ e), y e := by
  -- Exchange the two sums: each `e` collects `∑_{i : θ_i ≤ ρ_e} (θ_i − θ_{i+1})`.
  have hswap : ∑ i ∈ range (numVals ρ c),
        (theta ρ c i - theta ρ c (i + 1)) * ∑ e ∈ univ.filter (fun e => theta ρ c i ≤ ρ e), y e =
      ∑ e, (∑ i ∈ (range (numVals ρ c)).filter (fun i => theta ρ c i ≤ ρ e),
        (theta ρ c i - theta ρ c (i + 1))) * y e := by
    simp only [mul_sum, sum_filter, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun e _ => sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [hswap]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  rcases (hc e).lt_or_eq with hlt | heq
  · -- `ρ_e = θ_j` for some `j`, and `θ_i ≤ θ_j` exactly for `i ≥ j`: the sum telescopes.
    obtain ⟨j, hj, hθj⟩ := exists_theta_eq hlt
    have hset : (range (numVals ρ c)).filter (fun i => theta ρ c i ≤ ρ e) =
        Ico j (numVals ρ c) := by
      ext i
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨hi, hle⟩
        rw [← hθj] at hle
        exact ⟨(theta_le_theta_iff hi hj).1 hle, hi⟩
      · rintro ⟨hji, hi⟩
        refine ⟨hi, ?_⟩
        rw [← hθj]
        exact (theta_le_theta_iff hi hj).2 hji
    rw [hset, sum_Ico_theta_sub hj.le, hθj]
  · -- `ρ_e = c` lies below every `θ_i`: the sum is empty.
    rw [← heq, sub_self, eq_comm]
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hi, hle⟩ := mem_filter.1 hi
    exact absurd hle (not_le.2 (c_lt_theta (mem_range.1 hi)))

/-- Every level set `{e | ρ_e ≥ t}` with `t > c` is one of the `A_i` or empty (not in the paper:
the STOC version asserts "These are all nonempty positive level sets" without proof in the proof
of `prop:optchar`, `stoc-sections/appB-quadratic.tex:28`). -/
theorem levelSet_eq_theta {t : ℝ} (ht : c < t) :
    (univ.filter fun e => t ≤ ρ e) = ∅ ∨
      ∃ i < numVals ρ c,
        (univ.filter fun e => t ≤ ρ e) = univ.filter fun e => theta ρ c i ≤ ρ e := by
  by_cases hne : ((range (numVals ρ c)).filter fun i => t ≤ theta ρ c i).Nonempty
  · -- `i` is the largest index with `t ≤ θ_i`; then `θ_{i+1} < t`.
    obtain ⟨i, hi, hmax⟩ := ((range (numVals ρ c)).filter fun i => t ≤ theta ρ c i).exists_max_image
      id hne
    obtain ⟨hik, hti⟩ := mem_filter.1 hi
    have hik' := mem_range.1 hik
    have hnext : theta ρ c (i + 1) < t := by
      by_cases hi1 : i + 1 < numVals ρ c
      · by_contra h
        have := hmax (i + 1) (mem_filter.2 ⟨mem_range.2 hi1, not_lt.1 h⟩)
        simp only [id] at this
        omega
      · rw [theta_of_le (not_lt.1 hi1)]
        exact ht
    refine Or.inr ⟨i, hik', ?_⟩
    ext e
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨j, hj, hθj⟩ := exists_theta_eq (ht.trans_le h)
      rw [← hθj] at h ⊢
      have hji : j ≤ i := by
        by_contra hji
        have : theta ρ c j ≤ theta ρ c (i + 1) := by
          rcases (show i + 1 ≤ j by omega).lt_or_eq with hlt | heq
          · exact (theta_lt_theta hlt hj.le).le
          · rw [heq]
        linarith
      exact (theta_le_theta_iff hik' hj).2 hji
    · intro h
      exact hti.trans h
  · refine Or.inl (filter_eq_empty_iff.2 fun e _ h => hne ?_)
    obtain ⟨j, hj, hθj⟩ := exists_theta_eq (ht.trans_le h)
    exact ⟨j, mem_filter.2 ⟨mem_range.2 hj, hθj ▸ h⟩⟩

end

end Stoc
