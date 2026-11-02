-- stamp r8 2026-11-02
import Stoc.OptimalShare.Witness

/-!
# Networks of the type of Allman, Lo and McCormick

The networks of Theorem `thm:alm` and Theorem `thm:polybits` (ii) of the STOC version
(`stoc-sections/06-optimal-share.tex:58-78`), with the parts of the proofs that concern them:

* `cutCap`: the capacity of the cut `{s} ∪ S` in a network with a source `s`, a sink `s'` and the
  nodes `E`, source arcs `s → j` of capacity `a_j λ + b_j μ` and constant capacities `u_ij` on the
  arcs `i → j` and `u'_i` on the arcs `i → s'`; `IsUniqueMinCut`: `{s} ∪ S` is the unique minimum
  cut.
* `ALMNetwork`: what the proof of `thm:alm` (`stoc-sections/appB-quadratic.tex:518-534`) takes from
  Allman, Lo and McCormick (their Theorem 1.1 with the network of their Section 2).
* The first bounds of the sizes in the proof of `thm:polybits`, (5) in the numbering of
  `Stoc.PolyBit.polybits` ("Finally, for part (i), we show that all numbers have `O(n log n)` bits
  and that `f` can be evaluated in polynomial time.", `stoc-sections/appC-bits.tex:310-316`):
  `tau`, `t_le_tau`, `theta_le`, `D_le`, `K_le`; the bound `bound n = 2(n + 2)³ 9ⁿ τ³` of all
  numbers, and `size_bound_le` (`O(n log n)` bits).
* The proof of `thm:polybits` (ii), (6) in that numbering ("It remains to prove part (ii), for
  networks.", `appC-bits.tex:335-362`): `polybits_ii`, with `Xi`, `capC`, the capacities `arcU`,
  `arcS`, and the cut capacity `cutCap_eq`.
* `almNetwork`: the network that the proof of `thm:alm` cites, from the network of the proof of
  `thm:polybits` (ii) (not in the paper: the paper cites [ALM22, Theorem 1.1]).

The elements of `E = {1, …, n}` are `Fin n`, the element `e` being the paper's `e + 1`
(`Stoc.Witness.emb`); the numbers of `prop:witness` keep the paper's indices.
-/

namespace Stoc

namespace Network

open Finset Witness

/-! ### Networks and cuts -/

section Cuts

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The capacity of the cut `{s} ∪ S`, the total capacity of the arcs that leave `{s} ∪ S`, in a
network with a source `s`, a sink `s'` and the nodes `E`, with the arcs `s → j` of capacity
`a_j λ + b_j μ`, `i → j` of capacity `u_ij` and `i → s'` of capacity `u'_i`. -/
def cutCap (a b : E → ℝ) (u : E → E → ℝ) (u' : E → ℝ) (l μ : ℝ) (S : Finset E) : ℝ :=
  ∑ j ∈ univ \ S, (a j * l + b j * μ) + ∑ i ∈ S, u' i + ∑ i ∈ S, ∑ j ∈ univ \ S, u i j

/-- `{s} ∪ S` is the unique minimum cut at `(λ, μ)`. -/
def IsUniqueMinCut (a b : E → ℝ) (u : E → E → ℝ) (u' : E → ℝ) (l μ : ℝ) (S : Finset E) :
    Prop :=
  ∀ T, T ≠ S → cutCap a b u u' l μ S < cutCap a b u u' l μ T

variable (E) in
/-- What the proof of `thm:alm` takes from Allman, Lo and McCormick (`appB-quadratic.tex:519-525`,
their Theorem 1.1 with the network of their Section 2): a network with a source `s`, a sink `s'`
and the nodes `E`, arcs `s → j` of capacity `a_j λ + b_j θ` with `a_j, b_j > 0` and constant
nonnegative capacities on all other arcs, in which every `S ⊆ E` gives the unique minimum cut
`{s} ∪ S` at some point `(λ_S, θ_S) ∈ (0, 1)²`. -/
def ALMNetwork : Prop :=
  ∃ (a b : E → ℝ) (u : E → E → ℝ) (u' : E → ℝ), (∀ j, 0 < a j) ∧ (∀ j, 0 < b j) ∧
    (∀ i j, 0 ≤ u i j) ∧ (∀ i, 0 ≤ u' i) ∧ ∀ S : Finset E, ∃ l θ : ℝ, l ∈ Set.Ioo 0 1 ∧
      θ ∈ Set.Ioo 0 1 ∧ IsUniqueMinCut a b u u' l θ S

end Cuts

/-! ### The first bounds of the sizes in the proof of `thm:polybits` (part (i)) -/

section Bounds

/-- `τ = 2(2n + 2)^{n−1}`, the bound of `prop:witness` (i) on the `t_k`. -/
def tau (n : ℕ) : ℤ := 2 * (2 * n + 2) ^ (n - 1)

/-- The bound `2(n + 2)³ 9ⁿ τ³` on all numbers of the instance of `thm:polybits` (i) ("So all these
numbers are at most `2(n + 2)³ 9ⁿ τ³`"). -/
def bound (n : ℕ) : ℤ := 2 * (n + 2) ^ 3 * 9 ^ n * tau n ^ 3

lemma tau_pos (n : ℕ) : 0 < tau n := by unfold tau; positivity

lemma two_le_tau (n : ℕ) : 2 ≤ tau n := by
  unfold tau
  have : (1 : ℤ) ≤ (2 * n + 2) ^ (n - 1) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)])
  linarith

lemma bound_nonneg (n : ℕ) : 0 ≤ bound n := by unfold bound tau; positivity

/-- `(n + 2) 3ⁿ τ² ≤ 2 (n + 2)³ 9ⁿ τ³`. -/
lemma le_bound (n : ℕ) : (n + 2) * 3 ^ n * tau n * tau n ≤ bound n := by
  have hτ := two_le_tau n
  have h3 : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hn2 : (2 : ℤ) ≤ n + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)]
  have hX : (0 : ℤ) ≤ (n + 2) * 3 ^ n * tau n * tau n := by positivity
  have hY : (1 : ℤ) ≤ 2 * (n + 2) ^ 2 * 3 ^ n * tau n := by
    have : (1 : ℤ) ≤ (n + 2) ^ 2 := one_le_pow₀ (by linarith)
    have h4 : (1 : ℤ) ≤ (n + 2) ^ 2 * 3 ^ n := by nlinarith
    nlinarith
  have heq : bound n = (n + 2) * 3 ^ n * tau n * tau n * (2 * (n + 2) ^ 2 * 3 ^ n * tau n) := by
    unfold bound
    rw [show (9 : ℤ) ^ n = 3 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]
    ring
  rw [heq]
  nlinarith

/-- The sizes in the proof of `thm:polybits`: "By `prop:witness`(i), every `t_k` is at most
`τ := 2(2n + 2)^{n−1}`.": `t_k ≤ t_n ≤ τ` by the chain `t_1 < ⋯ < t_n ≤ 2(2n + 2)^{n−1}` of
`prop:witness` (i) (`Stoc.Witness.witness`). -/
lemma t_le_tau {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : t k ≤ tau n := by
  obtain ⟨-, hchain, hτ, -⟩ := (witness n (hk.trans hkn)).1
  rcases hkn.lt_or_eq with hlt | rfl
  · exact (chain_lt hchain hk hlt le_rfl).le.trans hτ
  · exact hτ

/-- `t_k > 0` for `k ≥ 1`, by `prop:witness` (i) (`Stoc.Witness.two_le_t`). -/
lemma t_pos {k : ℕ} (hk : 1 ≤ k) : 0 < t k := by linarith [two_le_t hk]

lemma lam_le {n k : ℕ} (hkn : k ≤ n) : lam k ≤ 3 ^ n := by
  unfold lam
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- The sizes in the proof of `thm:polybits`: "For `k ≥ 2`, we have `θ_k = 3^{k−1} t_{k−1} ≤ 3ⁿ τ`,
… and these bounds also hold for `k = 1`." -/
lemma theta_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : Witness.theta k ≤ 3 ^ n * tau n := by
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · rw [theta_one]
    exact (mul_pos (by positivity) (tau_pos n)).le
  · rw [theta_of_two_le hk2]
    exact mul_le_mul (lam_le hkn) (t_le_tau (by omega) (by omega)) (t_pos (by omega)).le
      (by positivity)

lemma d_le_theta {i k : ℕ} (hi : 1 ≤ i) : d i k ≤ Witness.theta k := by
  have : 0 ≤ lam k * t i := mul_nonneg (lam_pos k).le (t_pos hi).le
  rw [d]
  linarith

/-- The sizes in the proof of `thm:polybits`: "… so `D_k ≤ (k − 1) θ_k ≤ n 3ⁿ τ` …". -/
lemma D_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : D k ≤ n * 3 ^ n * tau n := by
  have h1 : D k ≤ (k - 1 : ℕ) * Witness.theta k := by
    calc D k ≤ ∑ _i ∈ Ico 1 k, Witness.theta k :=
          sum_le_sum fun i hi => d_le_theta (mem_Ico.1 hi).1
      _ = (k - 1 : ℕ) * Witness.theta k := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h2 : ((k - 1 : ℕ) : ℤ) ≤ n := by exact_mod_cast (show k - 1 ≤ n by omega)
  have h3 := theta_le hk hkn
  have h4 := theta_nonneg hk
  calc D k ≤ (k - 1 : ℕ) * Witness.theta k := h1
    _ ≤ n * (3 ^ n * tau n) := mul_le_mul h2 h3 h4 (by positivity)
    _ = n * 3 ^ n * tau n := by ring

/-- The sizes in the proof of `thm:polybits`: "… and `K_k = t_k λ̄_k + D_k + 1 ≤ (n + 2) 3ⁿ τ`,
…". -/
lemma K_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : K k ≤ (n + 2) * 3 ^ n * tau n := by
  have h1 : t k * lamBar k ≤ tau n * 3 ^ n := by
    have hlb : lamBar k ≤ 3 ^ n := by
      have := lam_eq hk
      have := lam_le hkn
      linarith [lamBar_nonneg k]
    exact mul_le_mul (t_le_tau hk hkn) hlb (lamBar_nonneg k) (tau_pos n).le
  have h2 := D_le hk hkn
  have h3 : (1 : ℤ) ≤ 3 ^ n * tau n := by
    have : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    nlinarith [tau_pos n]
  unfold K
  nlinarith

/-- `log₂ τ = O(n log n)`, and so all numbers below `bound n` have `O(n log n)` bits: for `n ≥ 1`,
`bound n` has at most `20 n (⌊log₂ n⌋ + 1)` binary digits. -/
lemma size_bound_le {n : ℕ} (hn : 1 ≤ n) :
    (bound n).toNat.size ≤ 20 * n * (Nat.log 2 n + 1) := by
  set L := Nat.log 2 n
  have hnL : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2L : 2 ≤ 2 ^ (L + 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (L + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 2 * n + 2 ≤ 2 ^ (L + 3) := by
    have : 2 ^ (L + 3) = 2 * 2 ^ (L + 2) := by ring
    have : 2 ^ (L + 2) = 2 * 2 ^ (L + 1) := by ring
    omega
  have hB : n + 2 ≤ 2 ^ (L + 3) := by omega
  -- `bound n ≤ 2^{4 + 13 n + 3 L n}` as natural numbers
  have hboundN : (bound n).toNat = 2 * (n + 2) ^ 3 * 9 ^ n * (2 * (2 * n + 2) ^ (n - 1)) ^ 3 := by
    unfold bound tau
    have : (2 * ((n : ℤ) + 2) ^ 3 * 9 ^ n * (2 * (2 * (n : ℤ) + 2) ^ (n - 1)) ^ 3) =
        ((2 * (n + 2) ^ 3 * 9 ^ n * (2 * (2 * n + 2) ^ (n - 1)) ^ 3 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hle : 2 * (n + 2) ^ 3 * 9 ^ n * (2 * (2 * n + 2) ^ (n - 1)) ^ 3 ≤
      2 ^ (4 + 13 * n + 3 * L * n) := by
    have e1 : (n + 2) ^ 3 ≤ (2 ^ (L + 3)) ^ 3 := Nat.pow_le_pow_left hB 3
    have e2 : 9 ^ n ≤ (2 ^ 4) ^ n := Nat.pow_le_pow_left (by norm_num) n
    have e3 : (2 * n + 2) ^ (n - 1) ≤ (2 ^ (L + 3)) ^ (n - 1) := Nat.pow_le_pow_left hA _
    calc 2 * (n + 2) ^ 3 * 9 ^ n * (2 * (2 * n + 2) ^ (n - 1)) ^ 3
        ≤ 2 * (2 ^ (L + 3)) ^ 3 * (2 ^ 4) ^ n * (2 * (2 ^ (L + 3)) ^ (n - 1)) ^ 3 := by
          gcongr
      _ = 2 ^ (1 + 3 * (L + 3) + 4 * n + 3 * (1 + (L + 3) * (n - 1))) := by
          rw [← pow_mul, ← pow_mul, ← pow_mul, show 2 * (2 : ℕ) ^ ((L + 3) * (n - 1)) =
            2 ^ (1 + (L + 3) * (n - 1)) by rw [pow_add, pow_one], ← pow_mul,
            show (2 : ℕ) * 2 ^ ((L + 3) * 3) = 2 ^ (1 + (L + 3) * 3) by rw [pow_add, pow_one]]
          rw [← pow_add, ← pow_add]
          congr 1
          ring
      _ ≤ 2 ^ (4 + 13 * n + 3 * L * n) := by
          apply Nat.pow_le_pow_right (by norm_num)
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          nlinarith
  rw [hboundN, Nat.size_le]
  calc 2 * (n + 2) ^ 3 * 9 ^ n * (2 * (2 * n + 2) ^ (n - 1)) ^ 3 ≤ 2 ^ (4 + 13 * n + 3 * L * n) :=
        hle
    _ < 2 ^ (20 * n * (L + 1)) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        nlinarith

end Bounds

/-! ### The proof of `thm:polybits` (ii): the network -/

section PartII

variable (n : ℕ)

/-- `Ξ = 1 + ∑_{k ∈ E} θ_k`. -/
noncomputable def Xi : ℤ := 1 + ∑ k ∈ Ico 1 (n + 1), Witness.theta k

/-- `C = 3ⁿ + Ξ`. -/
noncomputable def capC : ℤ := 3 ^ n + Xi n

/-- The capacity `d_i^{(k)}` of the arc `k → i` for `i < k`, and `0` for the other pairs. -/
noncomputable def arcU (e e' : Fin n) : ℤ := if e' < e then d (emb n e') (emb n e) else 0

/-- The capacity `K_k − D_k + Ξ + t_k` of the arc `k → s'`. -/
noncomputable def arcS (e : Fin n) : ℤ := K (emb n e) - D (emb n e) + Xi n + t (emb n e)

variable {n}

/-- `K_k − D_k + Ξ + t_k = t_k (λ̄_k + 1) + Ξ + 1`. -/
lemma arcS_eq (e : Fin n) : arcS n e = t (emb n e) * (lamBar (emb n e) + 1) + Xi n + 1 := by
  unfold arcS K
  ring

lemma theta_sum_nonneg : 0 ≤ ∑ k ∈ Ico 1 (n + 1), Witness.theta k :=
  sum_nonneg fun _ hk => theta_nonneg (mem_Ico.1 hk).1

lemma one_le_Xi : 1 ≤ Xi n := by unfold Xi; linarith [theta_sum_nonneg (n := n)]

/-- `D_k = ∑_{i<k} d_i^{(k)}`, over the elements `i < k` of `E`. -/
lemma D_emb (e : Fin n) :
    D (emb n e) = ∑ e' ∈ univ.filter (· < e), d (emb n e') (emb n e) := by
  have h : (univ.filter (· < e)).map (emb n) = Ico 1 (emb n e) := by
    ext j
    simp only [mem_map, mem_filter, mem_univ, true_and, mem_Ico, emb_apply]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact ⟨by omega, by simpa using Fin.lt_def.1 he'⟩
    · rintro ⟨hj1, hj2⟩
      exact ⟨⟨j - 1, by omega⟩, Fin.lt_def.2 (by simp; omega), by simp; omega⟩
  rw [D, ← h, sum_map]

/-- `g` on `S ⊆ E`, with the sums over `E`. -/
lemma g_map (S : Finset (Fin n)) :
    g (S.map (emb n)) = ∑ e ∈ S, K (emb n e) -
      ∑ e ∈ S, ∑ e' ∈ S.filter (· < e), d (emb n e') (emb n e) := by
  unfold g
  rw [sum_map, sum_map]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [filter_map, sum_map]
  congr 1
  refine filter_congr fun e' _ => ?_
  simp only [Function.comp_apply, emb_apply, Fin.lt_def]
  omega

/-- The proof of `thm:polybits` (ii): "As `D_k = ∑_{i<k} d_i^{(k)}`, every `S ⊆ E` satisfies
`∑_{k∈S} (K_k − D_k) + ∑_{k∈S, i∈E∖S, i<k} d_i^{(k)}
= ∑_{k∈S} K_k − ∑_{i,k∈S, i<k} d_i^{(k)} = g(S)`." -/
lemma sum_arc_eq_g (S : Finset (Fin n)) :
    ∑ e ∈ S, (K (emb n e) - D (emb n e)) + ∑ e ∈ S, ∑ e' ∈ univ \ S, arcU n e e' =
      g (S.map (emb n)) := by
  rw [g_map, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  have hsplit : univ.filter (· < e) = S.filter (· < e) ∪ (univ \ S).filter (· < e) := by
    ext e'
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff]
    tauto
  have hdisj : Disjoint (S.filter (· < e)) ((univ \ S).filter (· < e)) := by
    rw [disjoint_left]
    intro e' h1 h2
    exact (mem_sdiff.1 (mem_filter.1 h2).1).2 (mem_filter.1 h1).1
  have hcut : ∑ e' ∈ univ \ S, arcU n e e' =
      ∑ e' ∈ (univ \ S).filter (· < e), d (emb n e') (emb n e) := by
    rw [sum_filter]
    rfl
  rw [D_emb, hsplit, sum_union hdisj, hcut]
  ring

/-- The proof of `thm:polybits` (ii): "So the capacity of the cut `{s} ∪ S`, the total capacity of
the arcs that leave `{s} ∪ S`, is" `λ t(E) + μ n + F^g_{λ−1, Ξ−μ}(S)`, in the network with the
source arcs `t_j λ + μ`. -/
lemma cutCap_eq (l μ : ℝ) (S : Finset (Fin n)) :
    cutCap (tE n) (fun _ => 1) (fun e e' => (arcU n e e' : ℝ)) (fun e => (arcS n e : ℝ)) l μ S =
      l * ∑ e, tE n e + μ * n + F (gE n) (tE n) (l - 1, (Xi n : ℝ) - μ) S := by
  have hg : (gE n S : ℝ) = ∑ e ∈ S, ((K (emb n e) : ℝ) - D (emb n e)) +
      ∑ e ∈ S, ∑ e' ∈ univ \ S, (arcU n e e' : ℝ) := by
    simp only [gE]
    rw [← sum_arc_eq_g]
    push_cast
    rfl
  have hsd : ∑ j ∈ univ \ S, (tE n j * l + 1 * μ) =
      ∑ j, (tE n j * l + 1 * μ) - ∑ j ∈ S, (tE n j * l + 1 * μ) := by
    rw [← sum_sdiff (subset_univ S) (f := fun j => tE n j * l + 1 * μ)]
    ring
  simp only [cutCap, F, hg, arcS]
  push_cast
  rw [hsd]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← sum_mul]
  simp only [tE]
  ring

/-- Multiplying the coefficients of the source arcs by `C > 0` and dividing the parameters by
`C` keeps the capacities of all cuts. -/
lemma cutCap_scale {E : Type*} [Fintype E] [DecidableEq E] (a b : E → ℝ) (u : E → E → ℝ)
    (u' : E → ℝ) {C : ℝ} (hC : C ≠ 0) (l μ : ℝ) (S : Finset E) :
    cutCap (fun j => C * a j) (fun j => C * b j) u u' (l / C) (μ / C) S =
      cutCap a b u u' l μ S := by
  unfold cutCap
  congr 2
  refine sum_congr rfl fun j _ => ?_
  field_simp

lemma lamS_le (S : Finset (Fin n)) : ∑ j ∈ S.map (emb n), lam j ≤ lamBar (n + 1) := by
  rw [lamBar]
  refine sum_le_sum_of_subset_of_nonneg (fun _ hj => mem_Ico.2 (lt_of_mem_map_emb hj))
    fun j _ _ => (lam_pos j).le

lemma thetaS_le (S : Finset (Fin n)) :
    ∑ j ∈ S.map (emb n), Witness.theta j ≤ ∑ k ∈ Ico 1 (n + 1), Witness.theta k :=
  sum_le_sum_of_subset_of_nonneg (fun _ hj => mem_Ico.2 (lt_of_mem_map_emb hj))
    fun _ hj _ => theta_nonneg (mem_Ico.1 hj).1

lemma wit_eq (S : Finset (Fin n)) :
    wit n S = (((∑ j ∈ S.map (emb n), lam j : ℤ) : ℝ),
      ((∑ j ∈ S.map (emb n), Witness.theta j : ℤ) : ℝ)) := by
  simp only [wit, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
  push_cast
  exact ⟨rfl, rfl⟩

/-- **`thm:polybits` (ii)**, with its proof (`stoc-sections/appC-bits.tex:335-362`, "It remains to
prove part (ii), for networks."): there is a network of type [ALM22] with a source, a sink, `n`
further nodes and integral capacities at most `bound n` (so of `O(n log n)` bits, `size_bound_le`;
nonnegative, as the capacities of a network are), except that the arc from the source to node `j`
has capacity `a_j λ + b_j μ` for two parameters `(λ, μ)` and positive integers `a_j, b_j` at most
`bound n`, in which every cut `{s} ∪ S` is the unique minimum cut at some point of `(0, 1)²` whose
coordinates are quotients `p/r`, `q/r` of integers at most `bound n`.

The paper's steps: (1) the network with `Ξ = 1 + ∑_k θ_k`, arcs `k → i` of capacity
`d_i^{(k)}` for `i < k`, arcs `k → s'` of capacity `K_k − D_k + Ξ + t_k = t_k (λ̄_k + 1) + Ξ + 1`
and arcs `s → j` of capacity `t_j λ + μ`, all constant capacities nonnegative integers;
(2) `∑_{k∈S} (K_k − D_k) + ∑_{k∈S, i∉S, i<k} d_i^{(k)} = g(S)` (`sum_arc_eq_g`); (3) the capacity
of `{s} ∪ S` is `λ t(E) + μ n + F^g_{λ−1, Ξ−μ}(S)` (`cutCap_eq`); (4) by `prop:witness` (ii),
`{s} ∪ S` is the unique minimum cut at `(λ_S + 1, Ξ − θ_S)`; (5) both coordinates lie in `[1, C)`
for `C = 3ⁿ + Ξ`; (6) with `a_j = C t_j` and `b_j = C`, every cut `{s} ∪ S` is the unique minimum
cut at the point `((λ_S + 1)/C, (Ξ − θ_S)/C) ∈ (0, 1)²` (`cutCap_scale`); (7) by the bounds shown
for part (i), all capacities and coordinates are integers or quotients of integers at most
`bound n`. -/
theorem polybits_ii (hn : 1 ≤ n) :
    ∃ (a b : Fin n → ℤ) (u : Fin n → Fin n → ℤ) (u' : Fin n → ℤ),
      (∀ j, 0 < a j ∧ a j ≤ bound n) ∧ (∀ j, 0 < b j ∧ b j ≤ bound n) ∧
      (∀ i j, 0 ≤ u i j ∧ u i j ≤ bound n) ∧ (∀ i, 0 ≤ u' i ∧ u' i ≤ bound n) ∧
      ∀ S : Finset (Fin n), ∃ p q r : ℤ, 0 < p ∧ p < r ∧ 0 < q ∧ q < r ∧ r ≤ bound n ∧
        IsUniqueMinCut (fun j => (a j : ℝ)) (fun j => (b j : ℝ)) (fun i j => (u i j : ℝ))
          (fun i => (u' i : ℝ)) ((p : ℝ) / r) ((q : ℝ) / r) S := by
  have hτ := tau_pos n
  have h3n : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hθsum := theta_sum_nonneg (n := n)
  -- (1) "Let `Ξ := 1 + ∑_{k∈E} θ_k`, and consider the network with a source `s`, a sink `s'` and
  -- the nodes `E`, with an arc `k → i` of capacity `d_i^{(k)}` for all `i < k`, an arc `k → s'` of
  -- capacity `K_k − D_k + Ξ + t_k = t_k (λ̄_k + 1) + Ξ + 1` for all `k ∈ E`, and an arc `s → j`
  -- of capacity `t_j λ + μ` for all `j ∈ E`. All constant capacities are nonnegative integers."
  have hu : ∀ e e', 0 ≤ arcU n e e' := fun e e' => by
    unfold arcU
    split_ifs with h
    · exact d_nonneg (by simp)
        (by simp only [emb_apply]; exact Nat.add_lt_add_right (Fin.lt_def.1 h) 1)
    · exact le_rfl
  have hu' : ∀ e, 0 ≤ arcS n e := fun e => by
    rw [arcS_eq]
    have := t_pos (k := emb n e) (by simp)
    have := lamBar_nonneg (emb n e)
    have := one_le_Xi (n := n)
    positivity
  -- (2) and (3): the capacity of the cut `{s} ∪ S` (`sum_arc_eq_g`, `cutCap_eq`).
  -- (4) "By `prop:witness`(ii), the cut `{s} ∪ S` is therefore the unique minimum cut at
  -- `(λ, μ) = (λ_S + 1, Ξ − θ_S)`."
  have hmin : ∀ S : Finset (Fin n), IsUniqueMinCut (tE n) (fun _ => 1)
      (fun e e' => (arcU n e e' : ℝ)) (fun e => (arcS n e : ℝ))
      ((wit n S).1 + 1) ((Xi n : ℝ) - (wit n S).2) S := by
    intro S T hT
    have hw := (witness n hn).2.2 S T hT
    rw [cutCap_eq, cutCap_eq]
    have h1 : ((wit n S).1 + 1 - 1, (Xi n : ℝ) - ((Xi n : ℝ) - (wit n S).2)) = wit n S := by
      ext <;> simp
    rw [h1]
    linarith
  -- (5) "Both coordinates of this point lie in `[1, C)` for `C := 3ⁿ + Ξ`."
  set C := capC n with hC_def
  have hC : C = 3 ^ n + Xi n := rfl
  have hlamS : ∀ S : Finset (Fin n), 1 ≤ ∑ j ∈ S.map (emb n), lam j + 1 ∧
      ∑ j ∈ S.map (emb n), lam j + 1 < C := fun S => by
    refine ⟨by linarith [sum_nonneg fun j (_ : j ∈ S.map (emb n)) => (lam_pos j).le], ?_⟩
    have h1 := lamS_le S
    have h2 := lam_eq (k := n + 1) (by omega)
    have h3 : lam (n + 1) = 3 ^ n := by simp [lam]
    have := one_le_Xi (n := n)
    rw [hC]
    linarith [lamBar_nonneg (n + 1)]
  have hthS : ∀ S : Finset (Fin n), 1 ≤ Xi n - ∑ j ∈ S.map (emb n), Witness.theta j ∧
      Xi n - ∑ j ∈ S.map (emb n), Witness.theta j < C := fun S => by
    have h1 := thetaS_le S
    have h2 : 0 ≤ ∑ j ∈ S.map (emb n), Witness.theta j :=
      sum_nonneg fun j hj => theta_nonneg (lt_of_mem_map_emb hj).1
    rw [hC]
    constructor
    · unfold Xi; linarith
    · linarith
  have hCpos : (0 : ℤ) < C := by have := hlamS ∅; linarith
  -- (6) "So after the coefficients `t_j` and `1` of the arcs `s → j` are multiplied by `C`
  -- (that is, `a_j := C t_j` and `b_j := C`), every cut `{s} ∪ S` is the unique minimum cut at
  -- the point `((λ_S + 1)/C, (Ξ − θ_S)/C) ∈ (0, 1)²`." (By (5), `0 < λ_S + 1 < C` and
  -- `0 < Ξ − θ_S < C`.)
  have hscaled : ∀ S : Finset (Fin n), IsUniqueMinCut (fun j => ((C * t (emb n j) : ℤ) : ℝ))
      (fun _ => ((C : ℤ) : ℝ)) (fun e e' => (arcU n e e' : ℝ)) (fun e => (arcS n e : ℝ))
      (((∑ j ∈ S.map (emb n), lam j + 1 : ℤ) : ℝ) / (C : ℝ))
      (((Xi n - ∑ j ∈ S.map (emb n), Witness.theta j : ℤ) : ℝ) / (C : ℝ)) S := by
    intro S T hT
    have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast hCpos.ne'
    have hscale := fun T => cutCap_scale (tE n) (fun _ => (1 : ℝ))
      (fun e e' => (arcU n e e' : ℝ)) (fun e => (arcS n e : ℝ)) hC0
      ((wit n S).1 + 1) ((Xi n : ℝ) - (wit n S).2) T
    have h1 := hmin S T hT
    rw [← hscale S, ← hscale T] at h1
    rw [wit_eq] at h1
    convert h1 using 2 <;> simp [tE]
  -- (7) "By the bounds shown for part (i), all capacities and all coordinates of these points have
  -- `O(n log n)` bits": they are at most `bound n`.
  have hXi : Xi n ≤ 1 + n * (3 ^ n * tau n) := by
    have : ∑ k ∈ Ico 1 (n + 1), Witness.theta k ≤ ∑ _k ∈ Ico 1 (n + 1), 3 ^ n * tau n :=
      sum_le_sum fun k hk => theta_le (mem_Ico.1 hk).1 (by have := (mem_Ico.1 hk).2; omega)
    rw [sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul] at this
    unfold Xi
    linarith
  have hCle : C ≤ (n + 2) * 3 ^ n * tau n := by
    rw [hC]
    nlinarith
  have hb1 : (n + 2) * 3 ^ n * tau n ≤ bound n := by
    have h1 := le_bound n
    have h2 : (0 : ℤ) ≤ (n + 2) * 3 ^ n * tau n := by
      have := two_le_tau n
      positivity
    nlinarith [two_le_tau n]
  have hCt : ∀ j : Fin n, C * t (emb n j) ≤ bound n := fun j => by
    have ht := t_le_tau (n := n) (k := emb n j) (by simp) (by simp [Nat.succ_le_of_lt j.isLt])
    have htp := t_pos (k := emb n j) (by simp)
    have h1 : C * t (emb n j) ≤ (n + 2) * 3 ^ n * tau n * tau n :=
      mul_le_mul hCle ht htp.le (by positivity)
    linarith [le_bound n]
  have hUle : ∀ e e', arcU n e e' ≤ bound n := fun e e' => by
    unfold arcU
    split_ifs with h
    · have h1 := d_le_theta (i := emb n e') (k := emb n e) (by simp)
      have h2 := theta_le (n := n) (k := emb n e) (by simp) (by simp [Nat.succ_le_of_lt e.isLt])
      have h3 : 3 ^ n * tau n ≤ (n + 2) * 3 ^ n * tau n := by
        have : (0 : ℤ) ≤ 3 ^ n * tau n := by positivity
        have : (1 : ℤ) ≤ n + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)]
        nlinarith
      linarith
    · exact bound_nonneg n
  have hSle : ∀ e, arcS n e ≤ bound n := fun e => by
    rw [arcS_eq]
    have ht := t_le_tau (n := n) (k := emb n e) (by simp) (by simp [Nat.succ_le_of_lt e.isLt])
    have hlb : lamBar (emb n e) + 1 ≤ 3 ^ n := by
      have h1 := lam_eq (k := emb n e) (by simp)
      have h2 := lam_le (n := n) (k := emb n e) (by simp [Nat.succ_le_of_lt e.isLt])
      linarith [lamBar_nonneg (emb n e)]
    have htp := t_pos (k := emb n e) (by simp)
    have h1 : t (emb n e) * (lamBar (emb n e) + 1) ≤ tau n * 3 ^ n :=
      mul_le_mul ht hlb (by linarith [lamBar_nonneg (emb n e)]) hτ.le
    have h2 : (2 : ℤ) ≤ 3 ^ n * tau n := by nlinarith [two_le_tau n]
    have h3 : t (emb n e) * (lamBar (emb n e) + 1) + Xi n + 1 ≤ (n + 2) * 3 ^ n * tau n := by
      have : (n + 2) * 3 ^ n * tau n = n * (3 ^ n * tau n) + 2 * (3 ^ n * tau n) := by ring
      rw [this]
      linarith
    linarith
  refine ⟨fun j => C * t (emb n j), fun _ => C, arcU n, arcS n,
    fun j => ⟨mul_pos hCpos (t_pos (by simp)), hCt j⟩, fun _ => ⟨hCpos, hCle.trans hb1⟩,
    fun e e' => ⟨hu e e', hUle e e'⟩, fun e => ⟨hu' e, hSle e⟩, fun S => ?_⟩
  obtain ⟨hlam0, hlamC⟩ := hlamS S
  obtain ⟨hth0, hthC⟩ := hthS S
  exact ⟨∑ j ∈ S.map (emb n), lam j + 1, Xi n - ∑ j ∈ S.map (emb n), Witness.theta j, C,
    by linarith, hlamC, by linarith, hthC, hCle.trans hb1, hscaled S⟩

end PartII

/-- **Allman, Lo and McCormick, Theorem 1.1** with the network of their Section 2, in the form the
proof of `thm:alm` uses it (`ALMNetwork`) (not in the paper: the paper cites [ALM22, Theorem 1.1];
proved here from the network of the proof of `thm:polybits` (ii), `polybits_ii`). The hypothesis
`n ≥ 1` is that of `thm:alm`. -/
theorem almNetwork {n : ℕ} (hn : 1 ≤ n) : ALMNetwork (Fin n) := by
  obtain ⟨a, b, u, u', ha, hb, hu, hu', hS⟩ := polybits_ii hn
  refine ⟨fun j => (a j : ℝ), fun j => (b j : ℝ), fun i j => (u i j : ℝ), fun i => (u' i : ℝ),
    fun j => show (0 : ℝ) < a j by exact_mod_cast (ha j).1,
    fun j => show (0 : ℝ) < b j by exact_mod_cast (hb j).1,
    fun i j => show (0 : ℝ) ≤ u i j by exact_mod_cast (hu i j).1,
    fun i => show (0 : ℝ) ≤ u' i by exact_mod_cast (hu' i).1, fun S => ?_⟩
  obtain ⟨p, q, r, hp, hpr, hq, hqr, -, hcut⟩ := hS S
  have hr : (0 : ℝ) < r := by exact_mod_cast hp.trans hpr
  refine ⟨p / r, q / r,
    ⟨div_pos (by exact_mod_cast hp) hr, (div_lt_one hr).2 (by exact_mod_cast hpr)⟩,
    ⟨div_pos (by exact_mod_cast hq) hr, (div_lt_one hr).2 (by exact_mod_cast hqr)⟩, hcut⟩

end Network

end Stoc
