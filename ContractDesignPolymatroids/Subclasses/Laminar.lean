-- stamp r8 2026-11-02
import ContractDesignPolymatroids.Subclasses.Partition
import ContractDesignPolymatroids.Subclasses.SupportShrinks
import ContractDesignPolymatroids.Subclasses.LinearPieces

/-!
# Laminar families, the forest, the functions `D_L` and `π_L`, and the pinning intervals

The STOC version, Section 3 (`stoc-sections/06-optimal-share.tex:80`: laminar polymatroids, their
constraint sets and their height, recalled at `appB-quadratic.tex:602-606`) and Appendix B.8
(`sec:A-subclasses`): the text between `thm:laminar` and `lem:E-laminarformula`
(`stoc-sections/appB-quadratic.tex:722-768`), which fixes the notation of the proof of
`thm:laminar`.

*  Laminar families and their height (`IsLaminar`, `height`).
*  (s1) "Every element `e` lies in some constraint set, since otherwise `x_e` would be unbounded
  on `P₊(f)`" (`Stoc.exists_mem_of_indepPoly_eq`, `Partition.lean`), and (s2) "If `m_e = 0`, then
  `x*_e(α) = 0` for all `α`, …" (`Stoc.bestResponse_eq_zero_of_reward_eq_zero`,
  `LaminarEnvelope.lean`).
*  (s3) the pinning intervals (`IsPinningInterval`, `pinning_intervals`): by `lem:supportmon`, the
  support changes at no more than `n` shares, which cut `(0, ∞)` into at most `n + 1` open
  intervals on which the support is constant.
*  (s4) for a pinning interval `I` with support `W`, `𝓛_W`, the constraint sets that contain an
  element of `W` (`meeting`); the forest (for a laminar family `𝓚`, which is `𝓛_W` in the
  lemmas), with the parent `par(L)` (`IsParent`), the children (`children`), the smallest
  constraint set `ℓ(e)` containing `e` (`IsEll`, `ell`) and `E_L = {e ∈ W | ℓ(e) = L}` (`own`).
*  (s5) `D_L(α, θ) = ∑_{e ∈ E_L} (α m_e − θ)/β_e + ∑_K min {f(K), D_K(α, θ)}` (eq:E-D), recursively
  over the forest (`Dfun`, `Dfun_eq`); "By induction over the forest, `D_L` is the minimum of
  finitely many affine functions `(α, θ) ↦ α t(U) − θ β⁻¹(U) + c` with `U ⊆ L ∩ W` and `c ∈ ℝ`,
  one of them with `U = L ∩ W`." (`IsMinAffine`, `isMinAffine_Dfun`); "So `D_L` is continuous,
  concave and piecewise affine, nondecreasing in `α` and nonincreasing in `θ`, and
  `D_L(α, θ) → −∞` for `θ → ∞`, as `L` contains an element of `W`." (`continuous_Dfun`,
  `concaveOn_Dfun`,
  `pwAffine_Dfun`, `monotone_Dfun`, `antitone_Dfun`, `tendsto_Dfun`).
*  (s6) `π_L(α) = max {θ ∈ ℝ | D_L(α, θ) ≥ f(L)}`, the water level at which `L` is exactly full,
  with `π_L(α) = −∞` if `D_L(α, θ) < f(L)` for all `θ` (`pressure`, `PiBot`); "The maximum exists,
  as `D_L` is continuous and nonincreasing in `θ` and tends to `−∞`." (`isGreatest_pressure`); "So
  `{θ : D_L(α, θ) ≥ f(L)} = (−∞, π_L(α)]`." (`setOf_le_Dfun_eq`); "In particular,
  `D_L(α, θ) < f(L)` for `θ > π_L(α)` and, by continuity, `D_L(α, π_L(α)) = f(L)` if
  `π_L(α) > −∞`." (`Dfun_lt_of_pressure_lt`, `Dfun_pressure`).
*  (s7) `Π_V = max {0, max_{L ⊇ V} π_L}` (`PiUp`), and "Since the constraint sets in `𝓛_W` that
  contain `par(V)` are those that contain `V`, except `V` itself, we have
  `Π_V = max {Π_{par(V)}, π_V}`, where `Π_{par(V)} := 0` for maximal `V`." (`PiPar`,
  `PiUp_eq_maxPi`).

The value `−∞` of the STOC version is encoded, not represented: `π_L(α) = −∞` is the predicate
`PiBot L α` (`D_L(α, θ) < f(L)` for all `θ`, the case of the definition), and otherwise
`pressure L α` is the real maximum of the definition (`isGreatest_pressure`). The paper's maxima of
values in `ℝ ∪ {−∞}`, `Π_V = max {0, max_{L ⊇ V} π_L}` and `max {θ, max_{V ⊇ L ⊇ ℓ(e)} π_L}` (in
the proof of `lem:E-laminarformula`), are maxima over the `L` with `¬ PiBot L α` (`maxPi`), as a
value `−∞` does not change a maximum. `π_L ≡ −∞` is `∀ α, PiBot L α`; by the proof of
`lem:E-laminarformula`, either `π_L ≡ −∞` or `π_L(α) > −∞` for every `α`
(`Stoc.pressure_eq_inf'`, `LaminarEnvelope.lean`).

Not in the paper (D3): the facts on the pinning intervals that the setup leaves implicit
(`pinning_intervals`), and the routine steps of the induction for `isMinAffine_Dfun` (a sum of
minima of affine functions is the minimum of the sums: `IsMinAffine.add`, `isMinAffine_sum`).

`t(S) = ∑_{e ∈ S} m_e/β_e` is `tA m β S` (`Partition.lean`) and `β⁻¹(S)` is `binv β S`.

Taken over on 2026-10-21 from `Paper/Subclasses/Laminar.lean` (the long paper's `lem:envelope`) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version. Adapted on
2026-10-28 to the STOC version after PR #88, which defines `π_L` through the recursion `D_L`
(eq:E-D) instead of a minimum over pools.
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [DecidableEq E]

/-- A family of nonempty sets is laminar if any two of its members are disjoint or one contains
the other (Section 3: a laminar polymatroid has such a family of constraint sets). -/
structure IsLaminar (𝓛 : Finset (Finset E)) : Prop where
  nonempty : ∀ L ∈ 𝓛, L.Nonempty
  disjoint_or_subset : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, Disjoint L L' ∨ L ⊆ L' ∨ L' ⊆ L

omit [DecidableEq E] in
theorem IsLaminar.subset {𝓛 𝓛' : Finset (Finset E)} (h : IsLaminar 𝓛) (h' : 𝓛' ⊆ 𝓛) :
    IsLaminar 𝓛' :=
  ⟨fun L hL => h.nonempty L (h' hL), fun L hL L' hL' => h.disjoint_or_subset L (h' hL) L' (h' hL')⟩

omit [DecidableEq E] in
/-- Two constraint sets that share an element are nested. -/
theorem IsLaminar.subset_or_subset {𝓛 : Finset (Finset E)} (h : IsLaminar 𝓛) {L L' : Finset E}
    (hL : L ∈ 𝓛) (hL' : L' ∈ 𝓛) {e : E} (he : e ∈ L) (he' : e ∈ L') : L ⊆ L' ∨ L' ⊆ L := by
  rcases h.disjoint_or_subset L hL L' hL' with hd | h | h
  · exact absurd he' (disjoint_left.1 hd he)
  · exact Or.inl h
  · exact Or.inr h

omit [DecidableEq E] in
/-- Two constraint sets that both contain a third one are nested. -/
theorem IsLaminar.subset_or_subset_of_subset {𝓛 : Finset (Finset E)} (h : IsLaminar 𝓛)
    {J L L' : Finset E} (hJ : J ∈ 𝓛) (hL : L ∈ 𝓛) (hL' : L' ∈ 𝓛) (hJL : J ⊆ L) (hJL' : J ⊆ L') :
    L ⊆ L' ∨ L' ⊆ L := by
  obtain ⟨e, he⟩ := h.nonempty J hJ
  exact h.subset_or_subset hL hL' (hJL he) (hJL' he)

open Classical in
/-- The height of `𝓛`: the largest number of constraint sets in a chain in `𝓛`. -/
def height (𝓛 : Finset (Finset E)) : ℕ :=
  (𝓛.powerset.filter fun C : Finset (Finset E) => IsChain (· ⊆ ·) (↑C : Set (Finset E))).sup card

omit [DecidableEq E] in
/-- A chain in `𝓛` has at most `height 𝓛` constraint sets. -/
theorem card_le_height {𝓛 C : Finset (Finset E)} (hC : C ⊆ 𝓛)
    (hchain : IsChain (· ⊆ ·) (C : Set (Finset E))) : C.card ≤ height 𝓛 := by
  classical
  exact le_sup (f := card) (mem_filter.2 ⟨mem_powerset.2 hC, hchain⟩)

/-- (s4) `𝓛_W`: the constraint sets of `𝓛` that contain an element of the support `W`; the others
are removed (`appB-quadratic.tex:730-733`). -/
def meeting (𝓛 : Finset (Finset E)) (W : Finset E) : Finset (Finset E) :=
  𝓛.filter fun L => (L ∩ W).Nonempty

/-! ### (s4) The forest -/

variable {𝓚 : Finset (Finset E)}

omit [DecidableEq E] in
/-- `P = par(L)`: the smallest constraint set in `𝓚` that properly contains `L`
(`appB-quadratic.tex:734-735`). -/
def IsParent (𝓚 : Finset (Finset E)) (L P : Finset E) : Prop :=
  P ∈ 𝓚 ∧ L ⊂ P ∧ ∀ P' ∈ 𝓚, L ⊂ P' → P ⊆ P'

open Classical in
/-- The children of `L`: the constraint sets `K` with `par(K) = L`
(`appB-quadratic.tex:735-736`). -/
def children (𝓚 : Finset (Finset E)) (L : Finset E) : Finset (Finset E) :=
  𝓚.filter fun K => IsParent 𝓚 K L

omit [DecidableEq E] in
theorem mem_children {L K : Finset E} : K ∈ children 𝓚 L ↔ K ∈ 𝓚 ∧ IsParent 𝓚 K L := by
  classical
  simp [children]

omit [DecidableEq E] in
theorem IsParent.unique {L P P' : Finset E} (h : IsParent 𝓚 L P) (h' : IsParent 𝓚 L P') :
    P = P' :=
  Subset.antisymm (h.2.2 P' h'.1 h'.2.1) (h'.2.2 P h.1 h.2.1)

omit [DecidableEq E] in
/-- A constraint set properly inside a constraint set `L` has a parent, which lies inside `L`. -/
theorem exists_isParent (h𝓚 : IsLaminar 𝓚) {J L : Finset E} (hJ : J ∈ 𝓚) (hL : L ∈ 𝓚)
    (hJL : J ⊂ L) : ∃ P, IsParent 𝓚 J P ∧ P ⊆ L := by
  classical
  have hne : (𝓚.filter fun P => J ⊂ P).Nonempty := ⟨L, mem_filter.2 ⟨hL, hJL⟩⟩
  obtain ⟨P, hP, hmin⟩ := exists_min_image _ card hne
  obtain ⟨hP𝓚, hJP⟩ := mem_filter.1 hP
  have hsub : ∀ P' ∈ 𝓚, J ⊂ P' → P ⊆ P' := by
    intro P' hP' hJP'
    rcases h𝓚.subset_or_subset_of_subset hJ hP𝓚 hP' hJP.subset hJP'.subset with h | h
    · exact h
    · exact (eq_of_subset_of_card_le h (hmin P' (mem_filter.2 ⟨hP', hJP'⟩))) ▸ Subset.refl _
  exact ⟨P, ⟨hP𝓚, hJP, hsub⟩, hsub L hL hJL⟩

omit [DecidableEq E] in
/-- A child of `L` lies properly inside `L`. -/
theorem ssubset_of_mem_children {L K : Finset E} (hK : K ∈ children 𝓚 L) : K ⊂ L :=
  (mem_children.1 hK).2.2.1

/-- Every constraint set properly inside a constraint set `L` lies in a child of `L`. -/
theorem exists_mem_children_superset (h𝓚 : IsLaminar 𝓚) {J L : Finset E} (hJ : J ∈ 𝓚)
    (hL : L ∈ 𝓚) (hJL : J ⊂ L) : ∃ K ∈ children 𝓚 L, J ⊆ K := by
  classical
  have hne : (𝓚.filter fun M => J ⊆ M ∧ M ⊂ L).Nonempty :=
    ⟨J, mem_filter.2 ⟨hJ, Subset.refl _, hJL⟩⟩
  obtain ⟨K, hK, hmax⟩ := exists_max_image _ card hne
  obtain ⟨hK𝓚, hJK, hKL⟩ := mem_filter.1 hK
  refine ⟨K, mem_children.2 ⟨hK𝓚, hL, hKL, fun P' hP' hKP' => ?_⟩, hJK⟩
  rcases h𝓚.subset_or_subset_of_subset hK𝓚 hL hP' hKL.subset hKP'.subset with h | h
  · exact h
  · -- `P' ⊆ L`: if `P' ⊂ L`, it would be a larger constraint set between `J` and `L`.
    by_contra hLP'
    have hP'L : P' ⊂ L := ssubset_of_subset_of_ne h fun heq => hLP' (heq ▸ Subset.refl _)
    have := hmax P' (mem_filter.2 ⟨hP', hJK.trans hKP'.subset, hP'L⟩)
    exact absurd (card_lt_card hKP') (not_lt.2 this)

omit [DecidableEq E] in
/-- Distinct children are disjoint. -/
theorem disjoint_of_mem_children (h𝓚 : IsLaminar 𝓚) {L K K' : Finset E}
    (hK : K ∈ children 𝓚 L) (hK' : K' ∈ children 𝓚 L) (hne : K ≠ K') : Disjoint K K' := by
  obtain ⟨hK𝓚, -, hKL, hKpar⟩ := mem_children.1 hK
  obtain ⟨hK'𝓚, -, hK'L, hK'par⟩ := mem_children.1 hK'
  rcases h𝓚.disjoint_or_subset K hK𝓚 K' hK'𝓚 with h | h | h
  · exact h
  · -- `K ⊂ K'` would put `L = par(K)` inside `K' ⊂ L`.
    exact absurd (hKpar K' hK'𝓚 (ssubset_of_subset_of_ne h hne)) (not_subset_of_ssubset hK'L)
  · exact absurd (hK'par K hK𝓚 (ssubset_of_subset_of_ne h (Ne.symm hne)))
      (not_subset_of_ssubset hKL)

/-- A nonempty set inside two children lies in only one. -/
theorem eq_of_subset_children (h𝓚 : IsLaminar 𝓚) {L K K' J : Finset E}
    (hK : K ∈ children 𝓚 L) (hK' : K' ∈ children 𝓚 L) (hJ : J.Nonempty) (hJK : J ⊆ K)
    (hJK' : J ⊆ K') : K = K' := by
  by_contra hne
  obtain ⟨e, he⟩ := hJ
  exact disjoint_left.1 (disjoint_of_mem_children h𝓚 hK hK' hne) (hJK he) (hJK' he)

omit [DecidableEq E] in
/-- `L = ℓ(e)`: the smallest constraint set in `𝓚` that contains `e`
(`appB-quadratic.tex:736-738`). -/
def IsEll (𝓚 : Finset (Finset E)) (e : E) (L : Finset E) : Prop :=
  L ∈ 𝓚 ∧ e ∈ L ∧ ∀ L' ∈ 𝓚, e ∈ L' → L ⊆ L'

omit [DecidableEq E] in
theorem exists_isEll (h𝓚 : IsLaminar 𝓚) {e : E} (he : ∃ L ∈ 𝓚, e ∈ L) : ∃ L, IsEll 𝓚 e L := by
  classical
  obtain ⟨L₀, hL₀, heL₀⟩ := he
  have hne : (𝓚.filter fun L => e ∈ L).Nonempty := ⟨L₀, mem_filter.2 ⟨hL₀, heL₀⟩⟩
  obtain ⟨L, hL, hmin⟩ := exists_min_image _ card hne
  obtain ⟨hL𝓚, heL⟩ := mem_filter.1 hL
  refine ⟨L, hL𝓚, heL, fun L' hL' heL' => ?_⟩
  rcases h𝓚.subset_or_subset hL𝓚 hL' heL heL' with h | h
  · exact h
  · exact (eq_of_subset_of_card_le h (hmin L' (mem_filter.2 ⟨hL', heL'⟩))) ▸ Subset.refl _

open Classical in
/-- `ℓ(e)`: the smallest constraint set in `𝓚` that contains `e` (`∅` if there is none). -/
def ell (𝓚 : Finset (Finset E)) (e : E) : Finset E :=
  if h : ∃ L, IsEll 𝓚 e L then h.choose else ∅

omit [DecidableEq E] in
theorem isEll_ell (h𝓚 : IsLaminar 𝓚) {e : E} (he : ∃ L ∈ 𝓚, e ∈ L) : IsEll 𝓚 e (ell 𝓚 e) := by
  have h := exists_isEll h𝓚 he
  simp only [ell, h, dite_true]
  exact h.choose_spec

omit [DecidableEq E] in
/-- If `ℓ(e)` is a constraint set, then `e ∈ ℓ(e)`. -/
theorem mem_ell_of_mem (h𝓚 : IsLaminar 𝓚) {e : E} {L : Finset E} (hL : L ∈ 𝓚)
    (h : ell 𝓚 e = L) : e ∈ L := by
  classical
  by_cases hex : ∃ L', IsEll 𝓚 e L'
  · have := (isEll_ell h𝓚 ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2.1⟩)
    rw [h] at this
    exact this.2.1
  · simp only [ell, hex, dite_false] at h
    obtain ⟨x, hx⟩ := h𝓚.nonempty L hL
    rw [← h] at hx
    exact absurd hx (notMem_empty x)

open Classical in
/-- `E_L = {e ∈ W | ℓ(e) = L}`, the elements whose smallest constraint set is `L`
(`appB-quadratic.tex:738-739`). -/
def own (𝓚 : Finset (Finset E)) (W L : Finset E) : Finset E :=
  W.filter fun e => ell 𝓚 e = L

theorem mem_own {W L : Finset E} {e : E} : e ∈ own 𝓚 W L ↔ e ∈ W ∧ ell 𝓚 e = L := by
  classical
  simp [own]

/-- The sets `K ∩ W` of the children `K` of `L` are pairwise disjoint. -/
theorem pairwiseDisjoint_children_inter (h𝓚 : IsLaminar 𝓚) (L W : Finset E) :
    (children 𝓚 L : Set (Finset E)).PairwiseDisjoint (· ∩ W) := by
  intro K hK K' hK' hne
  exact disjoint_of_subset_left inter_subset_left
    (disjoint_of_subset_right inter_subset_left (disjoint_of_mem_children h𝓚 hK hK' hne))

/-- `L ∩ W` is the union of `E_L` and the sets `K ∩ W` of the children `K` of `L`. -/
theorem inter_eq_own_union (h𝓚 : IsLaminar 𝓚) {L : Finset E} (hL : L ∈ 𝓚) (W : Finset E) :
    L ∩ W = own 𝓚 W L ∪ (children 𝓚 L).biUnion (· ∩ W) := by
  ext e
  constructor
  · intro he
    obtain ⟨heL, heW⟩ := mem_inter.1 he
    have hℓ := isEll_ell h𝓚 ⟨L, hL, heL⟩
    by_cases hℓL : ell 𝓚 e = L
    · exact mem_union_left _ (mem_own.2 ⟨heW, hℓL⟩)
    · have hss : ell 𝓚 e ⊂ L := ssubset_of_subset_of_ne (hℓ.2.2 L hL heL) hℓL
      obtain ⟨K, hK, hℓK⟩ := exists_mem_children_superset h𝓚 hℓ.1 hL hss
      exact mem_union_right _ (mem_biUnion.2 ⟨K, hK, mem_inter.2 ⟨hℓK hℓ.2.1, heW⟩⟩)
  · intro he
    rcases mem_union.1 he with h | h
    · obtain ⟨heW, hℓ⟩ := mem_own.1 h
      exact mem_inter.2 ⟨mem_ell_of_mem h𝓚 hL hℓ, heW⟩
    · obtain ⟨K, hK, heK⟩ := mem_biUnion.1 h
      exact mem_inter.2 ⟨(ssubset_of_mem_children hK).subset (mem_inter.1 heK).1,
        (mem_inter.1 heK).2⟩

/-- `E_L` is disjoint from the sets `K ∩ W` of the children `K` of `L`. -/
theorem disjoint_own_biUnion (h𝓚 : IsLaminar 𝓚) (L W : Finset E) :
    Disjoint (own 𝓚 W L) ((children 𝓚 L).biUnion (· ∩ W)) := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨K, hK, heK⟩ := mem_biUnion.1 he'
  obtain ⟨-, hℓ⟩ := mem_own.1 he
  have hK𝓚 := (mem_children.1 hK).1
  have hℓK := (isEll_ell h𝓚 ⟨K, hK𝓚, (mem_inter.1 heK).1⟩).2.2 K hK𝓚 (mem_inter.1 heK).1
  rw [hℓ] at hℓK
  exact (not_subset_of_ssubset (ssubset_of_mem_children hK)) hℓK

/-- `L ∩ W` is the disjoint union of `E_L` and the sets `K ∩ W` of the children `K` of `L`. -/
theorem sum_inter_eq_own_add (h𝓚 : IsLaminar 𝓚) {L : Finset E} (hL : L ∈ 𝓚) (W : Finset E)
    (g : E → ℝ) :
    ∑ e ∈ L ∩ W, g e = ∑ e ∈ own 𝓚 W L, g e + ∑ K ∈ children 𝓚 L, ∑ e ∈ K ∩ W, g e := by
  rw [← sum_biUnion (pairwiseDisjoint_children_inter h𝓚 L W), inter_eq_own_union h𝓚 hL W,
    sum_union (disjoint_own_biUnion h𝓚 L W)]

/-! ### (s5) The functions `D_L` -/

/-- `β⁻¹(S) = ∑_{e ∈ S} 1/β_e`. -/
def binv (β : E → ℝ) (S : Finset E) : ℝ := ∑ e ∈ S, 1 / β e

omit [DecidableEq E] in
theorem binv_nonneg {β : E → ℝ} (hβ : ∀ e, 0 < β e) (S : Finset E) : 0 ≤ binv β S :=
  sum_nonneg fun e _ => (one_div_pos.2 (hβ e)).le

omit [DecidableEq E] in
theorem binv_pos {β : E → ℝ} (hβ : ∀ e, 0 < β e) {S : Finset E} (hS : S.Nonempty) :
    0 < binv β S :=
  sum_pos (fun e _ => one_div_pos.2 (hβ e)) hS

/-- (s5) **(eq:E-D)** (`appB-quadratic.tex:739-744`): for `L ∈ 𝓛_W` and `(α, θ) ∈ ℝ²`, recursively
over the forest,
`D_L(α, θ) = ∑_{e ∈ E_L} (α m_e − θ)/β_e + ∑_{K child of L} min {f(K), D_K(α, θ)}`. (The recursion
runs over the children `K ⊊ L`, `Finset.strongInduction`; the unfolded form is `Dfun_eq`.) -/
def Dfun (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ) :
    Finset E → ℝ → ℝ → ℝ :=
  Finset.strongInduction fun L D α θ =>
    ∑ e ∈ own 𝓚 W L, (α * m e - θ) / β e +
      ∑ K ∈ (children 𝓚 L).attach, min (f K.1) (D K.1 (ssubset_of_mem_children K.2) α θ)

variable {W : Finset E} {f : Finset E → ℝ} {m β : E → ℝ}

/-- **(eq:E-D)**, unfolded: `D_L(α, θ) = ∑_{e ∈ E_L} (α m_e − θ)/β_e + ∑_K min {f(K), D_K(α, θ)}`
over the children `K` of `L`. -/
theorem Dfun_eq (L : Finset E) (α θ : ℝ) :
    Dfun 𝓚 W f m β L α θ = ∑ e ∈ own 𝓚 W L, (α * m e - θ) / β e +
      ∑ K ∈ children 𝓚 L, min (f K) (Dfun 𝓚 W f m β K α θ) := by
  rw [Dfun, Finset.strongInduction_eq]
  congr 1
  exact sum_attach (children 𝓚 L) fun K => min (f K) (Dfun 𝓚 W f m β K α θ)

/-- The affine function `(α, θ) ↦ α t(U) − θ β⁻¹(U) + c` of a pair `p = (U, c)`. -/
def affU (m β : E → ℝ) (p : Finset E × ℝ) (α θ : ℝ) : ℝ :=
  α * tA m β p.1 - θ * binv β p.1 + p.2

omit [DecidableEq E] in
theorem affU_empty (m β : E → ℝ) (c α θ : ℝ) : affU m β (∅, c) α θ = c := by
  simp [affU, tA, binv]

/-- The affine function of `(U ∪ U', c + c')` is the sum of those of `(U, c)` and `(U', c')`, for
disjoint `U` and `U'`. -/
theorem affU_union {p q : Finset E × ℝ} (h : Disjoint p.1 q.1) (α θ : ℝ) :
    affU m β (p.1 ∪ q.1, p.2 + q.2) α θ = affU m β p α θ + affU m β q α θ := by
  simp only [affU, tA, binv, sum_union h]
  ring

omit [DecidableEq E] in
/-- `F` is the minimum of finitely many affine functions `(α, θ) ↦ α t(U) − θ β⁻¹(U) + c` with
`U ⊆ S` and `c ∈ ℝ`, one of them with `U = S` (the form of `D_L` in `appB-quadratic.tex:747-750`,
with `S = L ∩ W`). -/
def IsMinAffine (m β : E → ℝ) (S : Finset E) (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ P : Finset (Finset E × ℝ), ∃ hP : P.Nonempty, (∀ p ∈ P, p.1 ⊆ S) ∧ (∃ p ∈ P, p.1 = S) ∧
    ∀ α θ, F α θ = P.inf' hP fun p => affU m β p α θ

omit [DecidableEq E] in
/-- The sum `∑_{e ∈ S} (α m_e − θ)/β_e` is the affine function of `(S, 0)`. -/
theorem isMinAffine_own (S : Finset E) :
    IsMinAffine m β S fun α θ => ∑ e ∈ S, (α * m e - θ) / β e := by
  refine ⟨{(S, 0)}, singleton_nonempty _, fun p hp => by rw [mem_singleton.1 hp],
    ⟨_, mem_singleton_self _, rfl⟩, fun α θ => ?_⟩
  rw [inf'_singleton]
  simp only [affU, tA, binv, add_zero, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun e _ => by ring

omit [DecidableEq E] in
/-- `min {c, F}` adds the constant function `c`, the affine function of `(∅, c)`. -/
theorem IsMinAffine.min_const {S : Finset E} {F : ℝ → ℝ → ℝ} (h : IsMinAffine m β S F) (c : ℝ) :
    IsMinAffine m β S fun α θ => min c (F α θ) := by
  classical
  obtain ⟨P, hP, hsub, ⟨p₀, hp₀, hp₀S⟩, hF⟩ := h
  refine ⟨insert (∅, c) P, insert_nonempty _ _, fun p hp => ?_,
    ⟨p₀, mem_insert_of_mem hp₀, hp₀S⟩, fun α θ => ?_⟩
  · rcases mem_insert.1 hp with rfl | hp
    · exact empty_subset _
    · exact hsub p hp
  · show min c (F α θ) = _
    rw [inf'_insert, affU_empty, hF]

/-- (Not in the paper: a routine step of the induction over the forest for `isMinAffine_Dfun`.)
For disjoint `S` and `T`, the sum of a minimum of affine functions with `U ⊆ S` and one with
`U ⊆ T` is the minimum of the sums, affine functions with `U ⊆ S ∪ T`. -/
theorem IsMinAffine.add {S T : Finset E} {F G : ℝ → ℝ → ℝ} (hF : IsMinAffine m β S F)
    (hG : IsMinAffine m β T G) (hST : Disjoint S T) :
    IsMinAffine m β (S ∪ T) fun α θ => F α θ + G α θ := by
  obtain ⟨P, hP, hPS, ⟨p₀, hp₀, hp₀S⟩, hFP⟩ := hF
  obtain ⟨Q, hQ, hQT, ⟨q₀, hq₀, hq₀T⟩, hGQ⟩ := hG
  set g : (Finset E × ℝ) × (Finset E × ℝ) → Finset E × ℝ :=
    fun pq => (pq.1.1 ∪ pq.2.1, pq.1.2 + pq.2.2)
  have hdisj : ∀ pq ∈ P ×ˢ Q, Disjoint pq.1.1 pq.2.1 := fun pq hpq =>
    disjoint_of_subset_left (hPS _ (mem_product.1 hpq).1)
      (disjoint_of_subset_right (hQT _ (mem_product.1 hpq).2) hST)
  refine ⟨(P ×ˢ Q).image g, (hP.product hQ).image g, fun p hp => ?_,
    ⟨g (p₀, q₀), mem_image_of_mem g (mem_product.2 ⟨hp₀, hq₀⟩), by simp [g, hp₀S, hq₀T]⟩,
    fun α θ => ?_⟩
  · obtain ⟨pq, hpq, rfl⟩ := mem_image.1 hp
    exact union_subset_union (hPS _ (mem_product.1 hpq).1) (hQT _ (mem_product.1 hpq).2)
  · show F α θ + G α θ = _
    rw [hFP, hGQ, inf'_image]
    apply le_antisymm
    · refine le_inf' _ _ fun pq hpq => ?_
      simp only [Function.comp, g]
      rw [affU_union (hdisj pq hpq)]
      exact add_le_add (inf'_le _ (mem_product.1 hpq).1) (inf'_le _ (mem_product.1 hpq).2)
    · obtain ⟨p₁, hp₁, hp₁e⟩ := exists_mem_eq_inf' hP fun p => affU m β p α θ
      obtain ⟨q₁, hq₁, hq₁e⟩ := exists_mem_eq_inf' hQ fun q => affU m β q α θ
      have hpq : (p₁, q₁) ∈ P ×ˢ Q := mem_product.2 ⟨hp₁, hq₁⟩
      refine (inf'_le _ hpq).trans (le_of_eq ?_)
      simp only [Function.comp, g]
      rw [affU_union (hdisj _ hpq), hp₁e, hq₁e]

/-- (Not in the paper: a routine step of the induction over the forest for `isMinAffine_Dfun`.)
A finite sum of minima of affine functions with `U ⊆ S_i`, for pairwise disjoint `S_i`, is a minimum
of affine functions with `U ⊆ ⋃_i S_i` (`IsMinAffine.add`, by induction on the index set). -/
theorem isMinAffine_sum {ι : Type*} [DecidableEq ι] (I : Finset ι) {S : ι → Finset E}
    {F : ι → ℝ → ℝ → ℝ} (hdisj : (I : Set ι).PairwiseDisjoint S)
    (hF : ∀ i ∈ I, IsMinAffine m β (S i) (F i)) :
    IsMinAffine m β (I.biUnion S) fun α θ => ∑ i ∈ I, F i α θ := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨{(∅, 0)}, singleton_nonempty _, fun p hp => ?_, ⟨_, mem_singleton_self _, rfl⟩,
      fun α θ => ?_⟩
    · rw [mem_singleton.1 hp]
      exact empty_subset _
    · rw [inf'_singleton, affU_empty]
      exact sum_empty
  | insert i I hi ih =>
    have h1 := ih (hdisj.subset (by simp)) fun j hj => hF j (mem_insert_of_mem hj)
    have hdi : Disjoint (S i) (I.biUnion S) := by
      rw [disjoint_biUnion_right]
      intro j hj
      exact hdisj (mem_coe.2 (mem_insert_self i I)) (mem_coe.2 (mem_insert_of_mem hj))
        fun h => hi (h ▸ hj)
    have := (hF i (mem_insert_self i I)).add h1 hdi
    rw [biUnion_insert]
    simpa only [sum_insert hi] using this

/-- (s5) "By induction over the forest, `D_L` is the minimum of finitely many affine functions
`(α, θ) ↦ α t(U) − θ β⁻¹(U) + c` with `U ⊆ L ∩ W` and `c ∈ ℝ`, one of them with `U = L ∩ W`"
(`appB-quadratic.tex:747-750`): by (eq:E-D), `D_L` is the affine function of `E_L` plus, for each
child `K`, `min {f(K), D_K}`, which adds the constant function `f(K)` to the functions of `D_K`
(`IsMinAffine.min_const`); a sum of such minima is the minimum of the sums (`isMinAffine_sum`,
`IsMinAffine.add`), and `L ∩ W` is the disjoint union of `E_L` and the sets `K ∩ W`. -/
theorem isMinAffine_Dfun (h𝓚 : IsLaminar 𝓚) :
    ∀ L ∈ 𝓚, IsMinAffine m β (L ∩ W) (Dfun 𝓚 W f m β L) := by
  intro L
  induction L using Finset.strongInduction with
  | H L ih =>
  intro hL
  have hown := isMinAffine_own (m := m) (β := β) (own 𝓚 W L)
  have hch : IsMinAffine m β ((children 𝓚 L).biUnion (· ∩ W))
      fun α θ => ∑ K ∈ children 𝓚 L, min (f K) (Dfun 𝓚 W f m β K α θ) :=
    isMinAffine_sum _ (pairwiseDisjoint_children_inter h𝓚 L W) fun K hK =>
      (ih K (ssubset_of_mem_children hK) (mem_children.1 hK).1).min_const (f K)
  have h := hown.add hch (disjoint_own_biUnion h𝓚 L W)
  rw [← inter_eq_own_union h𝓚 hL W] at h
  have heq : Dfun 𝓚 W f m β L = fun α θ => ∑ e ∈ own 𝓚 W L, (α * m e - θ) / β e +
      ∑ K ∈ children 𝓚 L, min (f K) (Dfun 𝓚 W f m β K α θ) :=
    funext fun α => funext fun θ => Dfun_eq L α θ
  rw [heq]
  exact h

section MinAffine

variable {S : Finset E} {F : ℝ → ℝ → ℝ}

omit [DecidableEq E] in
/-- A minimum of finitely many affine functions is continuous. -/
theorem IsMinAffine.continuous (h : IsMinAffine m β S F) :
    Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
  obtain ⟨P, hP, -, -, hF⟩ := h
  simp only [hF]
  exact Continuous.finset_inf'_apply hP fun p _ => by unfold affU; fun_prop

omit [DecidableEq E] in
/-- The affine function of a pair commutes with convex combinations of points. -/
theorem affU_comb (p : Finset E × ℝ) (x y : ℝ × ℝ) {a b : ℝ} (hab : a + b = 1) :
    affU m β p (a * x.1 + b * y.1) (a * x.2 + b * y.2) =
      a * affU m β p x.1 x.2 + b * affU m β p y.1 y.2 := by
  unfold affU
  linear_combination (-p.2) * hab

omit [DecidableEq E] in
/-- A minimum of affine functions is concave. -/
theorem IsMinAffine.concaveOn (h : IsMinAffine m β S F) :
    ConcaveOn ℝ Set.univ fun p : ℝ × ℝ => F p.1 p.2 := by
  obtain ⟨P, hP, -, -, hF⟩ := h
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [hF, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  refine le_inf' hP _ fun p hp => ?_
  rw [affU_comb p x y hab]
  exact add_le_add (mul_le_mul_of_nonneg_left (inf'_le _ hp) ha)
    (mul_le_mul_of_nonneg_left (inf'_le _ hp) hb)

omit [DecidableEq E] in
/-- A minimum of finitely many affine functions is piecewise affine on `ℝ²`, as `lem:pwaffine`
states it for `x*`: finitely many convex sets cover `ℝ²`, and the function is affine on each, here
the sets on which one of the affine functions attains the minimum. -/
theorem IsMinAffine.pwAffine (h : IsMinAffine m β S F) :
    ∃ 𝓒 : Finset (Set (ℝ × ℝ)), (⋃ C ∈ 𝓒, C) = Set.univ ∧ ∀ C ∈ 𝓒, Convex ℝ C ∧
      ∃ a b c : ℝ, ∀ p ∈ C, F p.1 p.2 = a + b * p.1 + c * p.2 := by
  classical
  obtain ⟨P, hP, -, -, hF⟩ := h
  refine ⟨P.image fun p => {x : ℝ × ℝ | ∀ q ∈ P, affU m β p x.1 x.2 ≤ affU m β q x.1 x.2},
    ?_, fun C hC => ?_⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨p, hp, hpx⟩ := exists_mem_eq_inf' hP fun p => affU m β p x.1 x.2
    refine Set.mem_biUnion (mem_image_of_mem _ hp) fun q hq => ?_
    rw [← hpx]
    exact inf'_le _ hq
  · obtain ⟨p, hp, rfl⟩ := mem_image.1 hC
    refine ⟨fun x hx y hy a b ha hb hab => ?_, p.2, tA m β p.1, -binv β p.1, fun x hx => ?_⟩
    · rw [Set.mem_ofPred_eq] at hx hy ⊢
      intro q hq
      simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      rw [affU_comb p x y hab, affU_comb q x y hab]
      exact add_le_add (mul_le_mul_of_nonneg_left (hx q hq) ha)
        (mul_le_mul_of_nonneg_left (hy q hq) hb)
    · rw [hF, le_antisymm (inf'_le _ hp) (le_inf' hP _ fun q hq => hx q hq)]
      unfold affU
      ring

omit [DecidableEq E] in
/-- A minimum of affine functions `α t(U) − θ β⁻¹(U) + c` is nonincreasing in `θ`, as
`β⁻¹(U) ≥ 0`. -/
theorem IsMinAffine.antitone (hβ : ∀ e, 0 < β e) (h : IsMinAffine m β S F) (α : ℝ) :
    Antitone (F α) := by
  obtain ⟨P, hP, -, -, hF⟩ := h
  intro θ θ' hθ
  simp only [hF]
  refine le_inf' hP _ fun p hp => (inf'_le _ hp).trans ?_
  unfold affU
  have := binv_nonneg hβ p.1
  nlinarith

omit [DecidableEq E] in
/-- A minimum of affine functions `α t(U) − θ β⁻¹(U) + c` is nondecreasing in `α`, as
`t(U) ≥ 0` for `m ≥ 0`. -/
theorem IsMinAffine.monotone (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (h : IsMinAffine m β S F)
    (θ : ℝ) : Monotone fun α => F α θ := by
  obtain ⟨P, hP, -, -, hF⟩ := h
  intro α α' hα
  simp only [hF]
  refine le_inf' hP _ fun p hp => (inf'_le _ hp).trans ?_
  unfold affU
  have : 0 ≤ tA m β p.1 := sum_nonneg fun e _ => div_nonneg (hm e) (hβ e).le
  nlinarith

omit [DecidableEq E] in
/-- A minimum of affine functions `α t(U) − θ β⁻¹(U) + c`, one of them with `U = S`, tends to `−∞`
as `θ → ∞` if `S ≠ ∅`: it lies below the function of `S`, and `β⁻¹(S) > 0`. -/
theorem IsMinAffine.tendsto (hβ : ∀ e, 0 < β e) (h : IsMinAffine m β S F) (hS : S.Nonempty)
    (α : ℝ) : Tendsto (F α) atTop atBot := by
  obtain ⟨P, hP, -, ⟨p₀, hp₀, hp₀S⟩, hF⟩ := h
  have hb : 0 < binv β p₀.1 := hp₀S ▸ binv_pos hβ hS
  refine tendsto_atBot.2 fun B => ?_
  filter_upwards [eventually_ge_atTop ((α * tA m β p₀.1 + p₀.2 - B) / binv β p₀.1)] with θ hθ
  rw [hF]
  refine (inf'_le _ hp₀).trans ?_
  have := (div_le_iff₀ hb).1 hθ
  unfold affU
  linarith

end MinAffine

/-- (s5) "So `D_L` is continuous, …" (`appB-quadratic.tex:750`), as a minimum of finitely many
affine functions. -/
theorem continuous_Dfun (h𝓚 : IsLaminar 𝓚) {L : Finset E} (hL : L ∈ 𝓚) :
    Continuous fun p : ℝ × ℝ => Dfun 𝓚 W f m β L p.1 p.2 :=
  (isMinAffine_Dfun h𝓚 L hL).continuous

/-- (s5) "So `D_L` is … concave …" (`appB-quadratic.tex:750`). -/
theorem concaveOn_Dfun (h𝓚 : IsLaminar 𝓚) {L : Finset E} (hL : L ∈ 𝓚) :
    ConcaveOn ℝ Set.univ fun p : ℝ × ℝ => Dfun 𝓚 W f m β L p.1 p.2 :=
  (isMinAffine_Dfun h𝓚 L hL).concaveOn

/-- (s5) "So `D_L` is … piecewise affine, …" (`appB-quadratic.tex:750-751`). -/
theorem pwAffine_Dfun (h𝓚 : IsLaminar 𝓚) {L : Finset E} (hL : L ∈ 𝓚) :
    ∃ 𝓒 : Finset (Set (ℝ × ℝ)), (⋃ C ∈ 𝓒, C) = Set.univ ∧ ∀ C ∈ 𝓒, Convex ℝ C ∧
      ∃ a b c : ℝ, ∀ p ∈ C, Dfun 𝓚 W f m β L p.1 p.2 = a + b * p.1 + c * p.2 :=
  (isMinAffine_Dfun h𝓚 L hL).pwAffine

/-- (s5) "So `D_L` is … nondecreasing in `α` …" (`appB-quadratic.tex:751`). -/
theorem monotone_Dfun (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e)
    {L : Finset E} (hL : L ∈ 𝓚) (θ : ℝ) : Monotone fun α => Dfun 𝓚 W f m β L α θ :=
  (isMinAffine_Dfun h𝓚 L hL).monotone hβ hm θ

/-- (s5) "So `D_L` is … nonincreasing in `θ`, …" (`appB-quadratic.tex:751`). -/
theorem antitone_Dfun (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (α : ℝ) : Antitone (Dfun 𝓚 W f m β L α) :=
  (isMinAffine_Dfun h𝓚 L hL).antitone hβ α

/-- (s5) "… and `D_L(α, θ) → −∞` for `θ → ∞`, as `L` contains an element of `W`."
(`appB-quadratic.tex:751-753`). -/
theorem tendsto_Dfun (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (α : ℝ) : Tendsto (Dfun 𝓚 W f m β L α) atTop atBot :=
  (isMinAffine_Dfun h𝓚 L hL).tendsto hβ hLW α

/-! ### (s6) The water levels `π_L` -/

omit [DecidableEq E] in
/-- The paper's `π_L(α) = −∞`: `D_L(α, θ) < f(L)` for all `θ` (`appB-quadratic.tex:757-758`). -/
def PiBot (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (L : Finset E) (α : ℝ) : Prop :=
  ∀ θ, Dfun 𝓚 W f m β L α θ < f L

/-- (s6) `π_L(α) = max {θ ∈ ℝ | D_L(α, θ) ≥ f(L)}`, the water level at which `L` is exactly full
(`appB-quadratic.tex:754-758`). The paper's `π_L(α) := −∞` if `D_L(α, θ) < f(L)` for all `θ` is the
predicate `PiBot L α`; otherwise the maximum exists (`isGreatest_pressure`) and is this supremum.
-/
def pressure (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (L : Finset E) (α : ℝ) : ℝ :=
  sSup {θ | f L ≤ Dfun 𝓚 W f m β L α θ}

section WaterLevel

variable {L : Finset E} {α : ℝ}

/-- (s6) "The maximum exists, as `D_L` is continuous and nonincreasing in `θ` and tends to `−∞`."
(`appB-quadratic.tex:758-759`): for `π_L(α) > −∞`, `π_L(α)` is the greatest `θ` with
`D_L(α, θ) ≥ f(L)`. -/
theorem isGreatest_pressure (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (h : ¬ PiBot 𝓚 W f m β L α) :
    IsGreatest {θ | f L ≤ Dfun 𝓚 W f m β L α θ} (pressure 𝓚 W f m β L α) := by
  set T := {θ | f L ≤ Dfun 𝓚 W f m β L α θ}
  have hne : T.Nonempty := by
    simp only [PiBot, not_forall, not_lt] at h
    exact h
  have hcont : Continuous (Dfun 𝓚 W f m β L α) :=
    (continuous_Dfun h𝓚 hL).comp (Continuous.prodMk continuous_const continuous_id)
  have hanti := antitone_Dfun (W := W) (f := f) (m := m) h𝓚 hβ hL α
  -- `D_L(α, θ₀) < f(L)` for some `θ₀`, as `D_L(α, θ) → −∞`; so `T` lies below `θ₀`
  obtain ⟨θ₀, hθ₀⟩ := ((tendsto_Dfun (f := f) h𝓚 hβ hL hLW α).eventually
    (eventually_lt_atBot (f L))).exists
  have hbdd : BddAbove T := ⟨θ₀, fun θ (hθ : f L ≤ _) =>
    le_of_not_gt fun hlt => absurd (hθ.trans (hanti hlt.le)) (not_le.2 hθ₀)⟩
  have hclosed : IsClosed T := isClosed_le continuous_const hcont
  exact ⟨hclosed.csSup_mem hne hbdd, fun θ hθ => le_csSup hbdd hθ⟩

/-- (s6) "So `{θ : D_L(α, θ) ≥ f(L)} = (−∞, π_L(α)]`." (`appB-quadratic.tex:759-760`), for
`π_L(α) > −∞`. -/
theorem setOf_le_Dfun_eq (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (h : ¬ PiBot 𝓚 W f m β L α) :
    {θ | f L ≤ Dfun 𝓚 W f m β L α θ} = Set.Iic (pressure 𝓚 W f m β L α) := by
  have hG := isGreatest_pressure h𝓚 hβ hL hLW h
  ext θ
  exact ⟨fun hθ => hG.2 hθ,
    fun hθ => (hG.1 : f L ≤ _).trans (antitone_Dfun h𝓚 hβ hL α hθ)⟩

/-- (s6) "In particular, `D_L(α, θ) < f(L)` for `θ > π_L(α)` …" (`appB-quadratic.tex:761`), for
`π_L(α) > −∞`. -/
theorem Dfun_lt_of_pressure_lt (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (h : ¬ PiBot 𝓚 W f m β L α) {θ : ℝ}
    (hθ : pressure 𝓚 W f m β L α < θ) : Dfun 𝓚 W f m β L α θ < f L :=
  lt_of_not_ge fun hle => absurd ((isGreatest_pressure h𝓚 hβ hL hLW h).2 hle) (not_le.2 hθ)

/-- (s6) "… and, by continuity, `D_L(α, π_L(α)) = f(L)` if `π_L(α) > −∞`."
(`appB-quadratic.tex:761-762`): `D_L(α, π_L(α)) ≥ f(L)` as the maximum is attained, and
`D_L(α, θ) < f(L)` for `θ > π_L(α)`. -/
theorem Dfun_pressure (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (h : ¬ PiBot 𝓚 W f m β L α) :
    Dfun 𝓚 W f m β L α (pressure 𝓚 W f m β L α) = f L := by
  refine le_antisymm ?_ (isGreatest_pressure h𝓚 hβ hL hLW h).1
  have hc : Continuous (Dfun 𝓚 W f m β L α) :=
    (continuous_Dfun h𝓚 hL).comp (Continuous.prodMk continuous_const continuous_id)
  refine le_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto (Dfun 𝓚 W f m β L α) (𝓝[>] (pressure 𝓚 W f m β L α)) _)
    (eventually_nhdsWithin_of_forall fun θ hθ => ?_)
  exact (Dfun_lt_of_pressure_lt h𝓚 hβ hL hLW h hθ).le

end WaterLevel

/-! ### (s7) Maxima of the water levels -/

open Classical in
/-- The paper's `max {θ, max_{L ∈ 𝓢} π_L(α)}` of values in `ℝ ∪ {−∞}`: a value `π_L(α) = −∞`
(`PiBot L α`) does not change the maximum, so it is the maximum of `θ` and of the values `π_L(α)`
of the `L ∈ 𝓢` with `¬ PiBot L α`. -/
def maxPi (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (𝓢 : Finset (Finset E)) (θ α : ℝ) : ℝ :=
  (insert θ ((𝓢.filter fun L => ¬ PiBot 𝓚 W f m β L α).image fun L =>
    pressure 𝓚 W f m β L α)).max' (insert_nonempty _ _)

/-- (s7) `Π_V(α) = max {0, max_{L ⊇ V} π_L(α)}`, where `L` runs over the constraint sets in `𝓚`
that contain `V` (`appB-quadratic.tex:763-765`); as in `maxPi`, the values `π_L(α) = −∞` do not
contribute. -/
def PiUp (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (V : Finset E) (α : ℝ) : ℝ :=
  maxPi 𝓚 W f m β (𝓚.filter fun L => V ⊆ L) 0 α

open Classical in
/-- (s7) `Π_{par(V)}(α)`, with `Π_{par(V)} := 0` for a maximal `V`
(`appB-quadratic.tex:767-768`). -/
def PiPar (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (V : Finset E) (α : ℝ) : ℝ :=
  if h : ∃ P, IsParent 𝓚 V P then PiUp 𝓚 W f m β h.choose α else 0

section MaxPi

variable {𝓢 𝓣 : Finset (Finset E)} {θ α c : ℝ} {L : Finset E}

theorem le_maxPi (𝓢 : Finset (Finset E)) (θ α : ℝ) : θ ≤ maxPi 𝓚 W f m β 𝓢 θ α :=
  le_max' _ _ (mem_insert_self _ _)

theorem pressure_le_maxPi (hL : L ∈ 𝓢) (hgood : ¬ PiBot 𝓚 W f m β L α) (θ : ℝ) :
    pressure 𝓚 W f m β L α ≤ maxPi 𝓚 W f m β 𝓢 θ α := by
  classical
  unfold maxPi
  exact le_max' _ _ (mem_insert_of_mem (mem_image_of_mem (fun L => pressure 𝓚 W f m β L α)
    (mem_filter.2 ⟨hL, hgood⟩)))

theorem maxPi_le (hθ : θ ≤ c)
    (h : ∀ L ∈ 𝓢, ¬ PiBot 𝓚 W f m β L α → pressure 𝓚 W f m β L α ≤ c) :
    maxPi 𝓚 W f m β 𝓢 θ α ≤ c := by
  classical
  refine max'_le _ _ _ fun x hx => ?_
  rcases mem_insert.1 hx with rfl | hx
  · exact hθ
  · obtain ⟨L, hL, rfl⟩ := mem_image.1 hx
    exact h L (mem_filter.1 hL).1 (mem_filter.1 hL).2

/-- `max {θ, max_{𝓢 ∪ 𝓣}} = max {max {θ, max_𝓣}, max_𝓢}`. -/
theorem maxPi_union (𝓢 𝓣 : Finset (Finset E)) (θ α : ℝ) :
    maxPi 𝓚 W f m β (𝓢 ∪ 𝓣) θ α = maxPi 𝓚 W f m β 𝓢 (maxPi 𝓚 W f m β 𝓣 θ α) α := by
  apply le_antisymm
  · refine maxPi_le ((le_maxPi _ _ _).trans (le_maxPi _ _ _)) fun L hL hgood => ?_
    rcases mem_union.1 hL with hL | hL
    · exact pressure_le_maxPi hL hgood _
    · exact (pressure_le_maxPi hL hgood _).trans (le_maxPi _ _ _)
  · refine maxPi_le (maxPi_le (le_maxPi _ _ _) fun L hL hgood =>
      pressure_le_maxPi (mem_union_right _ hL) hgood _) fun L hL hgood =>
        pressure_le_maxPi (mem_union_left _ hL) hgood _

theorem maxPi_eq_left (h : ∀ L ∈ 𝓢, ¬ PiBot 𝓚 W f m β L α → pressure 𝓚 W f m β L α ≤ θ) :
    maxPi 𝓚 W f m β 𝓢 θ α = θ :=
  le_antisymm (maxPi_le le_rfl h) (le_maxPi _ _ _)

theorem maxPi_singleton (hgood : ¬ PiBot 𝓚 W f m β L α) (θ : ℝ) :
    maxPi 𝓚 W f m β {L} θ α = max θ (pressure 𝓚 W f m β L α) :=
  le_antisymm (maxPi_le (le_max_left _ _) fun _ hL' _ => (mem_singleton.1 hL') ▸ le_max_right _ _)
    (max_le (le_maxPi _ _ _) (pressure_le_maxPi (mem_singleton_self L) hgood _))

end MaxPi

theorem PiPar_eq {V P : Finset E} (h : IsParent 𝓚 V P) (α : ℝ) :
    PiPar 𝓚 W f m β V α = PiUp 𝓚 W f m β P α := by
  have hex : ∃ P, IsParent 𝓚 V P := ⟨P, h⟩
  rw [PiPar, dite_eq_left hex, hex.choose_spec.unique h]

theorem PiPar_eq_zero {V : Finset E} (h : ¬ ∃ P, IsParent 𝓚 V P) (α : ℝ) :
    PiPar 𝓚 W f m β V α = 0 := by
  rw [PiPar, dite_eq_right h]

/-- The constraint sets containing `V` with parent `P` are `V` and the constraint sets containing
`P` (`appB-quadratic.tex:765-767`). -/
theorem filter_supset_eq_insert {V P : Finset E} (hV : V ∈ 𝓚) (hP : IsParent 𝓚 V P) :
    𝓚.filter (fun L => V ⊆ L) = insert V (𝓚.filter fun L => P ⊆ L) := by
  classical
  ext L
  simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨hL, hVL⟩
    by_cases h : L = V
    · exact Or.inl h
    · exact Or.inr ⟨hL, hP.2.2 L hL (ssubset_of_subset_of_ne hVL (Ne.symm h))⟩
  · rintro (rfl | ⟨hL, hPL⟩)
    · exact ⟨hV, Subset.refl _⟩
    · exact ⟨hL, hP.2.1.subset.trans hPL⟩

/-- A constraint set without parent lies in no other constraint set. -/
theorem filter_supset_eq_singleton (h𝓚 : IsLaminar 𝓚) {V : Finset E} (hV : V ∈ 𝓚)
    (hP : ¬ ∃ P, IsParent 𝓚 V P) : 𝓚.filter (fun L => V ⊆ L) = {V} := by
  classical
  ext L
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hL, hVL⟩
    by_contra h
    obtain ⟨P, hP', -⟩ := exists_isParent h𝓚 hV hL (ssubset_of_subset_of_ne hVL (Ne.symm h))
    exact hP ⟨P, hP'⟩
  · rintro rfl
    exact ⟨hV, Subset.refl _⟩

/-- (s7) "Since the constraint sets in `𝓛_W` that contain `par(V)` are those that contain `V`,
except `V` itself, we have `Π_V = max {Π_{par(V)}, π_V}`, where `Π_{par(V)} := 0` for maximal
`V`." (`appB-quadratic.tex:765-768`). -/
theorem PiUp_eq_maxPi (h𝓚 : IsLaminar 𝓚) {V : Finset E} (hV : V ∈ 𝓚) (α : ℝ) :
    PiUp 𝓚 W f m β V α = maxPi 𝓚 W f m β {V} (PiPar 𝓚 W f m β V α) α := by
  by_cases hP : ∃ P, IsParent 𝓚 V P
  · obtain ⟨P, hP⟩ := hP
    rw [PiPar_eq hP, PiUp, PiUp, filter_supset_eq_insert hV hP, insert_eq, maxPi_union]
  · rw [PiPar_eq_zero hP, PiUp, filter_supset_eq_singleton h𝓚 hV hP]

/-- For `e ∈ V`, `Π_{ℓ(e)} = max {Π_{par(V)}, max_{V ⊇ L ⊇ ℓ(e)} π_L}`
(`appB-quadratic.tex:824-825`): a constraint set containing `ℓ(e)` lies inside `V` or contains
`par(V)`. -/
theorem PiUp_ell_eq (h𝓚 : IsLaminar 𝓚) {V : Finset E} (hV : V ∈ 𝓚) {e : E} (he : e ∈ V)
    (α : ℝ) :
    PiUp 𝓚 W f m β (ell 𝓚 e) α =
      maxPi 𝓚 W f m β (𝓚.filter fun L => L ⊆ V ∧ ell 𝓚 e ⊆ L) (PiPar 𝓚 W f m β V α) α := by
  have hℓ := isEll_ell h𝓚 ⟨V, hV, he⟩
  have hℓV : ell 𝓚 e ⊆ V := hℓ.2.2 V hV he
  -- a constraint set containing `ℓ(e)` and `V` are nested, as both contain `e`
  have hnest : ∀ L ∈ 𝓚, ell 𝓚 e ⊆ L → L ⊆ V ∨ V ⊂ L := fun L hL hℓL => by
    rcases h𝓚.subset_or_subset hL hV (hℓL hℓ.2.1) he with h | h
    · exact Or.inl h
    · by_cases hLV : L = V
      · exact Or.inl hLV.subset
      · exact Or.inr (ssubset_of_subset_of_ne h (Ne.symm hLV))
  by_cases hP : ∃ P, IsParent 𝓚 V P
  · obtain ⟨P, hP⟩ := hP
    rw [PiPar_eq hP, PiUp, PiUp, ← maxPi_union]
    congr 1
    ext L
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hL, hℓL⟩
      rcases hnest L hL hℓL with h | h
      · exact Or.inl ⟨hL, h, hℓL⟩
      · exact Or.inr ⟨hL, hP.2.2 L hL h⟩
    · rintro (⟨hL, -, hℓL⟩ | ⟨hL, hPL⟩)
      · exact ⟨hL, hℓL⟩
      · exact ⟨hL, hℓV.trans (hP.2.1.subset.trans hPL)⟩
  · rw [PiPar_eq_zero hP, PiUp]
    congr 1
    ext L
    simp only [mem_filter]
    constructor
    · rintro ⟨hL, hℓL⟩
      rcases hnest L hL hℓL with h | h
      · exact ⟨hL, h, hℓL⟩
      · obtain ⟨P, hP', -⟩ := exists_isParent h𝓚 hV hL h
        exact absurd ⟨P, hP'⟩ hP
    · rintro ⟨hL, -, hℓL⟩
      exact ⟨hL, hℓL⟩

/-! ### (s3) The pinning intervals -/

section Pinning

variable [Fintype E] {f : Finset E → ℝ} {m β : E → ℝ}

/-- A pinning interval (`appB-quadratic.tex:727-730`): a connected component of the set of shares
`α > 0` at which the support of `x*` does not change; by `lem:supportmon` these are at most `n + 1`
open intervals on which the support is constant (`pinning_intervals`). -/
def IsPinningInterval (f : Finset E → ℝ) (m β : E → ℝ) (I : Set ℝ) : Prop :=
  I ∈ components (Set.Ioi 0 \ supportChanges f m β)

/-- **(s3)** of the setup of `thm:laminar` (`appB-quadratic.tex:727-730`): by `lem:supportmon`,
which holds for every polymatroid, the support changes at no more than `n` shares. These shares cut
`(0, ∞)` into at most `n + 1` open intervals on which the support is constant, the pinning
intervals. (The count of the intervals, and that a connected component of the shares without
support changes is an open interval with constant support, the STOC version leaves implicit.) -/
theorem pinning_intervals (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) :
    (supportChanges f m β).Finite ∧ (supportChanges f m β).ncard ≤ Fintype.card E ∧
      {I | IsPinningInterval f m β I}.Finite ∧
      {I | IsPinningInterval f m β I}.ncard ≤ Fintype.card E + 1 ∧
      (∀ I, IsPinningInterval f m β I → IsOpen I ∧ I.Nonempty ∧ I ⊆ Set.Ioi 0 ∧
        ∀ α ∈ I, ∀ α' ∈ I, brSupport f m β α = brSupport f m β α') ∧
      ∀ α, 0 < α → α ∈ supportChanges f m β ∨ ∃ I, IsPinningInterval f m β I ∧ α ∈ I := by
  obtain ⟨-, -, hfin, hcard⟩ := supportmon hf hβ hm
  have hT : Set.Ioi (0 : ℝ) \ supportChanges f m β = Set.Ioi 0 \ ↑hfin.toFinset := by
    rw [hfin.coe_toFinset]
  have hTcard : hfin.toFinset.card ≤ Fintype.card E := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hcard
  obtain ⟨hIfin, hIcard⟩ := components_finite_ncard_le Set.ordConnected_Ioi hfin.toFinset
  rw [← hT] at hIfin hIcard
  refine ⟨hfin, hcard, hIfin, hIcard.trans (by omega), fun I hI => ?_, fun α hα => ?_⟩
  · obtain ⟨α, hα, rfl⟩ := hI
    have hopen : IsOpen (Set.Ioi (0 : ℝ) \ supportChanges f m β) :=
      isOpen_Ioi.sdiff hfin.isClosed
    have hsub := connectedComponentIn_subset (Set.Ioi (0 : ℝ) \ supportChanges f m β) α
    refine ⟨hopen.connectedComponentIn, ⟨α, mem_connectedComponentIn hα⟩,
      fun x hx => (hsub hx).1, fun α₁ h₁ α₂ h₂ => ?_⟩
    -- between two shares of the component there is no support change
    have hno : ∀ {a b : ℝ}, a ∈ connectedComponentIn (Set.Ioi 0 \ supportChanges f m β) α →
        b ∈ connectedComponentIn (Set.Ioi 0 \ supportChanges f m β) α → a ≤ b →
        brSupport f m β b = brSupport f m β a := fun ha hb hab =>
      brSupport_eq_of_noChange hf hβ hm (hsub ha).1 hab fun τ hτ hτab =>
        (hsub (isPreconnected_connectedComponentIn.Icc_subset ha hb hτab)).2 hτ
    rcases le_total α₁ α₂ with h | h
    · exact (hno h₁ h₂ h).symm
    · exact hno h₂ h₁ h
  · by_cases hc : α ∈ supportChanges f m β
    · exact Or.inl hc
    · exact Or.inr ⟨_, ⟨α, ⟨hα, hc⟩, rfl⟩, mem_connectedComponentIn ⟨hα, hc⟩⟩

end Pinning

end

end Stoc
