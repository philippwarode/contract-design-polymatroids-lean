-- stamp r8 2026-11-02
import ContractDesignPolymatroids.Subclasses.PressurePieces

/-!
# Counting along the forest

The STOC version, Appendix B.8 (`sec:A-subclasses`), Lemma `lem:E-piececount`, second inequality
(`stoc-sections/appB-quadratic.tex:866-873`), and the whole lemma (`piececount`).

The proof follows the STOC version; its steps (1)-(5), for the first inequality, are in
`ContractDesignPolymatroids/Subclasses/PressurePieces.lean`. With `Σ(L) = ∑_{J ⊆ L} #(J)` over the constraint sets `J`
in `𝓛_W` contained in `L` (`sumBelow`), `#(J)` the number of linear pieces of `π_J`
(`numPieces`):

6. the first inequality (`numPieces_le`) gives `Σ(L) ≤ 1 + 3 ∑_K Σ(K)` over the children `K` of
  `L` (`sumBelow_le`);
7. by induction, `Σ(L) ≤ ∑_{J ⊆ L} 3^{dist(L, J)}` (`sumBelow_le_sum_pow`), where
  `dist(L, J) ≤ h − 1` is the number of edges of the forest between `L` and `J` (`forestDist`,
  counted by their upper endpoints, `forestDist_le`);
8. summing over the maximal constraint sets in `𝓛_W` (`roots`, `sum_eq_sum_roots`) and using
  `|𝓛_W| ≤ |𝓛|` gives `∑_{L ∈ 𝓛_W} #(L) ≤ |𝓛| 3^{h−1}` (`sum_le_card_mul_pow`).

Not in the paper (D3): the constraint sets strictly inside `L` are the constraint sets inside the
children of `L` (`sum_ssubset_eq_sum_children`, used in steps (6) and (7)), and every constraint
set lies in exactly one maximal constraint set (`sum_eq_sum_roots`, step (8)); the STOC version uses
both without proof.

Taken over on 2026-10-21 from `Paper/Subclasses/LaminarCount.lean` (the long paper's
`lem:pressure-pieces`, whose proof the STOC version takes over) for the STOC version (`stoc.tex`);
from then on this copy follows the STOC version. Adapted on 2026-10-28 to the STOC version after
PR #88 (constraint sets `L`, `J`, `K`, and `#(L)` through the `π_L` defined by `D_L`).
-/

namespace Stoc

open Finset

variable {E : Type*} [DecidableEq E]
variable {𝓚 : Finset (Finset E)} {W : Finset E} {f : Finset E → ℝ} {m β : E → ℝ}

/-- "For the second inequality, let `Σ(L) := ∑_{J⊆L} #(J)`, where `J` runs over the constraint sets
in `𝓛_W` contained in `L`." (`appB-quadratic.tex:866-867`) Here `𝓚 = 𝓛_W` and
`#(J) = numPieces J`. -/
noncomputable def sumBelow (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (L : Finset E) : ℕ :=
  ∑ J ∈ 𝓚.filter (· ⊆ L), numPieces 𝓚 W f m β J

/-- `dist(L, J)`, the number of edges of the forest between `L` and a constraint set `J ⊆ L`
(`appB-quadratic.tex:870-871`), counted by their upper endpoints: the edges on the path from `J` up
to `L` are the pairs `(u', par(u'))`, and their upper endpoints `par(u')` are exactly the
constraint sets `u` with `J ⊊ u ⊆ L`. -/
def forestDist (𝓚 : Finset (Finset E)) (L J : Finset E) : ℕ :=
  (𝓚.filter fun u => J ⊂ u ∧ u ⊆ L).card

open Classical in
/-- The maximal constraint sets in `𝓚`: those without a parent. -/
noncomputable def roots (𝓚 : Finset (Finset E)) : Finset (Finset E) :=
  𝓚.filter fun r => ¬ ∃ P, IsParent 𝓚 r P

omit [DecidableEq E] in
theorem mem_roots {r : Finset E} : r ∈ roots 𝓚 ↔ r ∈ 𝓚 ∧ ¬ ∃ P, IsParent 𝓚 r P := by
  classical
  unfold roots
  exact mem_filter

/-- (Not in the paper: steps (6) and (7) of `lem:E-piececount` pass from the constraint sets
strictly inside `L` to the constraint sets inside the children of `L` without proof.) The
constraint sets strictly inside `L` are the constraint sets inside the children of `L`, each inside
exactly one child. -/
theorem sum_ssubset_eq_sum_children (h𝓚 : IsLaminar 𝓚) {L : Finset E} (hL : L ∈ 𝓚)
    {M : Type*} [AddCommMonoid M] (g : Finset E → M) :
    ∑ J ∈ 𝓚.filter (· ⊂ L), g J = ∑ K ∈ children 𝓚 L, ∑ J ∈ 𝓚.filter (· ⊆ K), g J := by
  have hdisj : (children 𝓚 L : Set (Finset E)).PairwiseDisjoint fun K => 𝓚.filter (· ⊆ K) := by
    intro K hK K' hK' hne
    refine disjoint_left.2 fun J hJ hJ' => hne ?_
    exact eq_of_subset_children h𝓚 hK hK' (h𝓚.nonempty J (mem_filter.1 hJ).1)
      (mem_filter.1 hJ).2 (mem_filter.1 hJ').2
  rw [← sum_biUnion hdisj]
  congr 1
  ext J
  simp only [mem_filter, mem_biUnion]
  constructor
  · rintro ⟨hJ, hJL⟩
    obtain ⟨K, hK, hJK⟩ := exists_mem_children_superset h𝓚 hJ hL hJL
    exact ⟨K, hK, hJ, hJK⟩
  · rintro ⟨K, hK, hJ, hJK⟩
    exact ⟨hJ, hJK.trans_ssubset (ssubset_of_mem_children hK)⟩

/-- The constraint sets contained in a constraint set `L` are `L` and the constraint sets strictly
inside `L`. -/
theorem filter_subset_eq_insert {L : Finset E} (hL : L ∈ 𝓚) :
    𝓚.filter (· ⊆ L) = insert L (𝓚.filter (· ⊂ L)) := by
  ext J
  simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨hJ, hJL⟩
    by_cases h : J = L
    · exact Or.inl h
    · exact Or.inr ⟨hJ, ssubset_of_subset_of_ne hJL h⟩
  · rintro (rfl | ⟨hJ, hJL⟩)
    · exact ⟨hL, Subset.refl _⟩
    · exact ⟨hJ, hJL.subset⟩

theorem notMem_filter_ssubset {L : Finset E} : L ∉ 𝓚.filter (· ⊂ L) := fun h =>
  ssubset_irrefl L (mem_filter.1 h).2

/-- **Step (6)** (`appB-quadratic.tex:867-868`): "The first inequality gives
`Σ(L) ≤ 1 + 3 ∑_K Σ(K)`, where `K` runs over the children of `L`, …" The first inequality is
`#(L) ≤ 1 + 2 ∑_{J ⊊ L} #(J)` (`numPieces_le`). -/
theorem sumBelow_le (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty)
    {L : Finset E} (hL : L ∈ 𝓚) :
    sumBelow 𝓚 W f m β L ≤ 1 + 3 * ∑ K ∈ children 𝓚 L, sumBelow 𝓚 W f m β K := by
  have h1 := numPieces_le (f := f) (m := m) h𝓚 hβ hmeet hL
  rw [sumBelow, filter_subset_eq_insert hL, sum_insert notMem_filter_ssubset]
  unfold sumBelow
  rw [← sum_ssubset_eq_sum_children h𝓚 hL]
  omega

theorem forestDist_self (L : Finset E) : forestDist 𝓚 L L = 0 := by
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun u _ hu => ?_)
  exact (not_subset_of_ssubset hu.1) hu.2

/-- The path from `J ⊆ K` up to `L = par(K)` has one edge more than the path up to `K`. -/
theorem forestDist_child (h𝓚 : IsLaminar 𝓚) {L K J : Finset E} (hK : K ∈ children 𝓚 L)
    (hJ : J ∈ 𝓚) (hJK : J ⊆ K) : forestDist 𝓚 L J = forestDist 𝓚 K J + 1 := by
  obtain ⟨hK𝓚, hKpar⟩ := mem_children.1 hK
  have hJL : J ⊂ L := hJK.trans_ssubset hKpar.2.1
  have hnot : L ∉ 𝓚.filter fun u => J ⊂ u ∧ u ⊆ K := fun h =>
    (not_subset_of_ssubset hKpar.2.1) (mem_filter.1 h).2.2
  have hset : (𝓚.filter fun u => J ⊂ u ∧ u ⊆ L) = insert L (𝓚.filter fun u => J ⊂ u ∧ u ⊆ K) := by
    ext u
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hu, hJu, huL⟩
      obtain ⟨e, he⟩ := h𝓚.nonempty J hJ
      rcases h𝓚.subset_or_subset hu hK𝓚 (hJu.subset he) (hJK he) with h | h
      · exact Or.inr ⟨hu, hJu, h⟩
      · by_cases hKu : K = u
        · subst hKu
          exact Or.inr ⟨hu, hJu, Subset.refl _⟩
        · exact Or.inl (Subset.antisymm huL (hKpar.2.2 u hu (ssubset_of_subset_of_ne h hKu)))
    · rintro (rfl | ⟨hu, hJu, huK⟩)
      · exact ⟨hKpar.1, hJL, Subset.refl _⟩
      · exact ⟨hu, hJu, huK.trans hKpar.2.1.subset⟩
  rw [forestDist, hset, card_insert_of_notMem hnot]
  rfl

/-- **Step (7)** (`appB-quadratic.tex:868-871`): "… and by induction
`Σ(L) ≤ ∑_{J⊆L} 3^{dist(L,J)}`, …" -/
theorem sumBelow_le_sum_pow (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e)
    (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty) :
    ∀ L ∈ 𝓚, sumBelow 𝓚 W f m β L ≤ ∑ J ∈ 𝓚.filter (· ⊆ L), 3 ^ forestDist 𝓚 L J := by
  intro L
  induction L using Finset.strongInduction with
  | H L ih =>
  intro hL
  have hK : ∀ K ∈ children 𝓚 L, 3 * sumBelow 𝓚 W f m β K ≤
      ∑ J ∈ 𝓚.filter (· ⊆ K), 3 ^ forestDist 𝓚 L J := by
    intro K hK
    rw [mul_comm]
    refine (Nat.mul_le_mul_right 3 (ih K (ssubset_of_mem_children hK) (mem_children.1 hK).1)).trans
      (le_of_eq ?_)
    rw [sum_mul]
    refine sum_congr rfl fun J hJ => ?_
    rw [forestDist_child h𝓚 hK (mem_filter.1 hJ).1 (mem_filter.1 hJ).2, pow_succ]
  -- (7) "… and by induction `Σ(L) ≤ ∑_{J⊆L} 3^{dist(L,J)}`, …"
  -- From `Σ(L) ≤ 1 + 3 ∑_K Σ(K)` (step (6)) and the induction hypothesis for the children `K`,
  -- with `dist(L, J) = dist(K, J) + 1` for `J ⊆ K`.
  calc sumBelow 𝓚 W f m β L ≤ 1 + 3 * ∑ K ∈ children 𝓚 L, sumBelow 𝓚 W f m β K :=
        sumBelow_le h𝓚 hβ hmeet hL
    _ ≤ 3 ^ forestDist 𝓚 L L +
        ∑ K ∈ children 𝓚 L, ∑ J ∈ 𝓚.filter (· ⊆ K), 3 ^ forestDist 𝓚 L J := by
        rw [forestDist_self, pow_zero, mul_sum]
        exact Nat.add_le_add_left (sum_le_sum hK) _
    _ = ∑ J ∈ 𝓚.filter (· ⊆ L), 3 ^ forestDist 𝓚 L J := by
        rw [filter_subset_eq_insert hL, sum_insert notMem_filter_ssubset,
          sum_ssubset_eq_sum_children h𝓚 hL]

/-- **Step (7)**: "… where `dist(L,J) ≤ h − 1` is the number of edges of the forest between `L` and
`J`.": the bound holds as `J` and the constraint sets `u` with `J ⊊ u ⊆ L` form a chain of
`dist(L, J) + 1` constraint sets (not in the paper: the proof states it without proof). -/
theorem forestDist_le (h𝓚 : IsLaminar 𝓚) {𝓛 : Finset (Finset E)} (h𝓚𝓛 : 𝓚 ⊆ 𝓛) {L J : Finset E}
    (hJ : J ∈ 𝓚) : forestDist 𝓚 L J ≤ height 𝓛 - 1 := by
  obtain ⟨e, he⟩ := h𝓚.nonempty J hJ
  set C := insert J (𝓚.filter fun u => J ⊂ u ∧ u ⊆ L)
  have hmem : ∀ u ∈ C, u ∈ 𝓚 ∧ J ⊆ u := by
    intro u hu
    rcases mem_insert.1 hu with rfl | hu
    · exact ⟨hJ, Subset.refl _⟩
    · exact ⟨(mem_filter.1 hu).1, (mem_filter.1 hu).2.1.subset⟩
  have hchain : IsChain (· ⊆ ·) (C : Set (Finset E)) := by
    intro u hu u' hu' _
    obtain ⟨hu𝓚, hJu⟩ := hmem u hu
    obtain ⟨hu'𝓚, hJu'⟩ := hmem u' hu'
    exact h𝓚.subset_or_subset hu𝓚 hu'𝓚 (hJu he) (hJu' he)
  have hcard := card_le_height (fun u hu => h𝓚𝓛 (hmem u hu).1) hchain
  have hnot : J ∉ 𝓚.filter fun u => J ⊂ u ∧ u ⊆ L := fun h =>
    ssubset_irrefl J (mem_filter.1 h).2.1
  rw [card_insert_of_notMem hnot] at hcard
  unfold forestDist
  omega

/-- (Not in the paper: step (8) of `lem:E-piececount`, "summing over the maximal constraint sets in
`𝓛_W`", uses without proof that every constraint set lies in exactly one maximal constraint set.)
In a laminar family every member lies in exactly one maximal member, so a sum over the family
splits along the maximal members. -/
theorem sum_eq_sum_roots (h𝓚 : IsLaminar 𝓚) {M : Type*} [AddCommMonoid M] (g : Finset E → M) :
    ∑ J ∈ 𝓚, g J = ∑ r ∈ roots 𝓚, ∑ J ∈ 𝓚.filter (· ⊆ r), g J := by
  classical
  have hroot : ∀ r ∈ roots 𝓚, r ∈ 𝓚 ∧ ¬ ∃ P, IsParent 𝓚 r P := fun r hr => mem_roots.1 hr
  have hdisj : (roots 𝓚 : Set (Finset E)).PairwiseDisjoint fun r => 𝓚.filter (· ⊆ r) := by
    intro r hr r' hr' hne
    refine disjoint_left.2 fun J hJ hJ' => ?_
    obtain ⟨hr𝓚, hrmax⟩ := hroot r hr
    obtain ⟨hr'𝓚, hr'max⟩ := hroot r' hr'
    obtain ⟨hJ𝓚, hJr⟩ := mem_filter.1 hJ
    rcases h𝓚.subset_or_subset_of_subset hJ𝓚 hr𝓚 hr'𝓚 hJr (mem_filter.1 hJ').2 with h | h
    · obtain ⟨P, hP, -⟩ := exists_isParent h𝓚 hr𝓚 hr'𝓚 (ssubset_of_subset_of_ne h hne)
      exact hrmax ⟨P, hP⟩
    · obtain ⟨P, hP, -⟩ := exists_isParent h𝓚 hr'𝓚 hr𝓚
        (ssubset_of_subset_of_ne h (Ne.symm hne))
      exact hr'max ⟨P, hP⟩
  rw [← sum_biUnion hdisj]
  congr 1
  ext J
  simp only [mem_biUnion, mem_filter]
  constructor
  · intro hJ
    -- the largest constraint set containing `J` has no parent
    have hne : (𝓚.filter fun r => J ⊆ r).Nonempty := ⟨J, mem_filter.2 ⟨hJ, Subset.refl _⟩⟩
    obtain ⟨r, hr, hmax⟩ := exists_max_image _ card hne
    obtain ⟨hr𝓚, hJr⟩ := mem_filter.1 hr
    refine ⟨r, mem_roots.2 ⟨hr𝓚, fun ⟨P, hP⟩ => ?_⟩, hJ, hJr⟩
    have := hmax P (mem_filter.2 ⟨hP.1, hJr.trans hP.2.1.subset⟩)
    exact absurd (card_lt_card hP.2.1) (not_lt.2 this)
  · rintro ⟨r, -, hJ, -⟩
    exact hJ

/-- **Steps (7) and (8)** (`appB-quadratic.tex:868-873`): "Summing over the maximal constraint sets
in `𝓛_W` and using `|𝓛_W| ≤ |𝓛|` gives the claim." For `𝓚 = 𝓛_W ⊆ 𝓛`,
`∑_{L ∈ 𝓚} #(L) ≤ |𝓛| 3^{h−1}`, `h` the height of `𝓛`: summing
`Σ(r) ≤ ∑_{J ⊆ r} 3^{dist(r, J)} ≤ ∑_{J ⊆ r} 3^{h−1}` over the maximal constraint sets `r` in
`𝓚`, and using `|𝓚| ≤ |𝓛|`. -/
theorem sum_le_card_mul_pow (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e)
    (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty) {𝓛 : Finset (Finset E)} (h𝓚𝓛 : 𝓚 ⊆ 𝓛) :
    ∑ L ∈ 𝓚, numPieces 𝓚 W f m β L ≤ 𝓛.card * 3 ^ (height 𝓛 - 1) := by
  have hr : ∀ r ∈ roots 𝓚, r ∈ 𝓚 := fun r hr => (mem_roots.1 hr).1
  -- (8) "Summing over the maximal constraint sets in `𝓛_W` …"
  calc ∑ L ∈ 𝓚, numPieces 𝓚 W f m β L = ∑ r ∈ roots 𝓚, sumBelow 𝓚 W f m β r :=
        sum_eq_sum_roots h𝓚 _
    -- (7) "… by induction `Σ(L) ≤ ∑_{J⊆L} 3^{dist(L,J)}`, where `dist(L,J) ≤ h − 1` …", here
    -- for the maximal constraint sets `r`
    _ ≤ ∑ r ∈ roots 𝓚, ∑ J ∈ 𝓚.filter (· ⊆ r), 3 ^ forestDist 𝓚 r J :=
        sum_le_sum fun r hr' => sumBelow_le_sum_pow h𝓚 hβ hmeet r (hr r hr')
    _ ≤ ∑ r ∈ roots 𝓚, ∑ J ∈ 𝓚.filter (· ⊆ r), 3 ^ (height 𝓛 - 1) :=
        sum_le_sum fun r _ => sum_le_sum fun J hJ =>
          Nat.pow_le_pow_right (by norm_num) (forestDist_le h𝓚 h𝓚𝓛 (mem_filter.1 hJ).1)
    -- (8) "… and using `|𝓛_W| ≤ |𝓛|` gives the claim."
    _ = 𝓚.card * 3 ^ (height 𝓛 - 1) := by
        rw [← sum_eq_sum_roots h𝓚 (fun _ => 3 ^ (height 𝓛 - 1)), sum_const, smul_eq_mul]
    _ ≤ 𝓛.card * 3 ^ (height 𝓛 - 1) := Nat.mul_le_mul_right _ (card_le_card h𝓚𝓛)

/-! ### The lemma -/

variable [Fintype E]

/-- **`lem:E-piececount`** (Lemma B.21, `stoc-sections/appB-quadratic.tex:835-874`): let `I` be a
pinning interval with support `W`. For `L ∈ 𝓛_W`, the number `#(L)` of linear pieces of `π_L` on `ℝ`
(`0` if `π_L ≡ −∞`, that is, if `∀ α, PiBot L α`) satisfies `#(L) ≤ 1 + 2 ∑_{J ⊊ L} #(J)`, where `J`
runs over the constraint sets in `𝓛_W` properly contained in `L`; consequently
`∑_{L ∈ 𝓛_W} #(L) ≤ |𝓛| 3^{h−1}`, `h` the height of `𝓛`. The STOC version's steps: (1)-(5) of the
first inequality, `Stoc.numPieces_le` (`ContractDesignPolymatroids/Subclasses/PressurePieces.lean`), and (6)-(8) of the
second inequality (`sumBelow_le`, `sumBelow_le_sum_pow`, `forestDist_le`, `sum_le_card_mul_pow`).
The pinning interval, `f`, `P₊(f)` and `m` enter only through the setup (`𝓛_W`, `D_L` and the
`π_L`). -/
theorem piececount (_hf : IsRankFunction f) {𝓛 : Finset (Finset E)} (h𝓛 : IsLaminar 𝓛)
    (_hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) (_hm : ∀ e, 0 ≤ m e) {I : Set ℝ} (_hI : IsPinningInterval f m β I)
    {W : Finset E} (_hW : ∀ α ∈ I, brSupport f m β α = W) :
    (∀ L ∈ meeting 𝓛 W, numPieces (meeting 𝓛 W) W f m β L ≤
        1 + 2 * ∑ J ∈ (meeting 𝓛 W).filter (· ⊂ L), numPieces (meeting 𝓛 W) W f m β J) ∧
      ∑ L ∈ meeting 𝓛 W, numPieces (meeting 𝓛 W) W f m β L ≤ 𝓛.card * 3 ^ (height 𝓛 - 1) := by
  have h𝓚 : IsLaminar (meeting 𝓛 W) := h𝓛.subset (filter_subset _ _)
  have hmeet : ∀ L ∈ meeting 𝓛 W, (L ∩ W).Nonempty := fun L hL => (mem_filter.1 hL).2
  have h1 : ∀ L ∈ meeting 𝓛 W, numPieces (meeting 𝓛 W) W f m β L ≤
      1 + 2 * ∑ J ∈ (meeting 𝓛 W).filter (· ⊂ L), numPieces (meeting 𝓛 W) W f m β J :=
    fun L hL => numPieces_le h𝓚 hβ hmeet hL
  exact ⟨h1, sum_le_card_mul_pow h𝓚 hβ hmeet (filter_subset _ _)⟩

end Stoc
