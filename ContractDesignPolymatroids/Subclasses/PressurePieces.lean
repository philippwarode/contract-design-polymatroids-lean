-- stamp r8 2026-11-02
import ContractDesignPolymatroids.Subclasses.LaminarEnvelope

/-!
# The linear pieces of the water levels

The STOC version, Appendix B.8 (`sec:A-subclasses`), Lemma `lem:E-piececount`, first inequality
(`stoc-sections/appB-quadratic.tex:835-841`, proof `:843-874`): let `I` be a pinning interval with
support `W`; for `L ∈ 𝓛_W`, the number `#(L)` of linear pieces of `π_L` on `ℝ` (`0` if
`π_L ≡ −∞`, `numPieces`) satisfies `#(L) ≤ 1 + 2 ∑_{J ⊊ L} #(J)` (`numPieces_le`).

The proof follows the STOC version:

1. `T_L = {(α, θ) | D_L(α, θ) ≥ f(L)}` is the hypograph of `π_L` (`Tset`, `Tset_eq`), and `D_L` is
  concave and piecewise affine on `ℝ²` (the setup, `Stoc.concaveOn_Dfun`, `Stoc.pwAffine_Dfun`);
  `T_L` is closed, as `D_L` is continuous (`isClosed_Tset`);
2. with `brk(F)` the set of points near which `F` is not affine (`brk`): near interior points of
  `T_K` the function `min {f(K), D_K}` equals `f(K)`, and near points outside `T_K` it equals
  `D_K`, so `brk(min {f(K), D_K}) ⊆ ∂T_K ∪ brk(D_K)` (`brk_min_subset`); by (eq:E-D), `brk(D_L)` is
  contained in the union of the sets `brk(min {f(K), D_K})` over the children `K` of `L`
  (`brk_D_subset_children`), and by induction `brk(D_L) ⊆ ⋃_{J ⊊ L} ∂T_J` (`brk_D_subset`);
3. let `z` be a vertex of the graph of `π_L`; then `D_L(z) = f(L)`, and `D_L` is not affine near
  `z`: otherwise, near `z`, the set `T_L` would be a half-plane bounded by a line through `z`, or a
  whole neighborhood of `z`, and in neither case would `z` be a vertex of the graph of `π_L`; so
  `z ∈ ∂T_J` for some `J ⊊ L`, that is, `z` lies on the graph of `π_J` (`exists_eq_of_mem_kinks`);
4. now let `γ` be a linear piece of the graph of some `π_J`, over a closed interval `O`; on `O`, the
  function `π_L − π_J` is concave, so its zero set in `O` consists of at most two points or is an
  interval, on whose interior `π_L = π_J` is affine; hence `γ` contains at most two vertices of the
  graph of `π_L` (`ncard_vertices_le_two`);
5. as this graph has `#(L) − 1` vertices, the first inequality follows (`numPieces_eq`,
  `numPieces_le`).

The linear pieces of `π_L` are the closures of the connected components of the points near which
`π_L` is affine (`Stoc.linPieces`, `ContractDesignPolymatroids/Subclasses/LinearPieces.lean`), closed intervals; a vertex
of the graph of `π_L` is a point `(α, π_L(α))` with `α` a kink of `π_L`, and is identified with `α`
where vertices are counted. The paper's `π_L ≡ −∞` is `∀ α, PiBot L α`
(`ContractDesignPolymatroids/Subclasses/Laminar.lean`): then `T_L = ∅` and `#(L) = 0`.

Not in the paper (D3), each in its own lemma: the graph of `π_L` lies on the boundary of its
hypograph `T_L`, and the boundary of `T_J` on the graph of `π_J` (`graph_mem_frontier`,
`frontier_Tset_subset`), used without proof in step (3); and the facts on the real line of
`ContractDesignPolymatroids/Subclasses/LinearPieces.lean` (the linear pieces and their count, the zero set of a concave
function, the boundary points of an interval), used without proof in steps (3)-(5).

Taken over on 2026-10-21 from `Paper/Subclasses/PressurePieces.lean` (the long paper's
`lem:pressure-pieces`, whose proof the STOC version takes over) for the STOC version (`stoc.tex`);
from then on this copy follows the STOC version. Adapted on 2026-10-28 to the STOC version after
PR #88 (`T_L = {D_L ≥ f(L)}`, and the one-dimensional argument of step (4) instead of a supporting
line).
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
variable {𝓚 : Finset (Finset E)} {W : Finset E} {f : Finset E → ℝ} {m β : E → ℝ}

/-- `T_L = {(α, θ) | D_L(α, θ) ≥ f(L)}` (`appB-quadratic.tex:844`). -/
def Tset (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (L : Finset E) : Set (ℝ × ℝ) :=
  {p | f L ≤ Dfun 𝓚 W f m β L p.1 p.2}

/-- "Let `brk(F)` denote the set of points near which a function `F` is not affine."
(`appB-quadratic.tex:846-847`) -/
def brk (F : ℝ × ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | ¬ ∃ a b c : ℝ, ∀ᶠ q in 𝓝 p, F q = a + b * q.1 + c * q.2}

open Classical in
/-- `#(L)`: the number of linear pieces of `π_L` on `ℝ`, and `#(L) = 0` if `π_L ≡ −∞`
(`appB-quadratic.tex:836-838`). -/
def numPieces (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (L : Finset E) : ℕ :=
  if ∀ α, PiBot 𝓚 W f m β L α then 0 else (linPieces (pressure 𝓚 W f m β L)).ncard

/-! ### Step (1): `T_L` -/

/-- **Step (1)** (`appB-quadratic.tex:844-845`): "The set `T_L := {(α, θ) : D_L(α, θ) ≥ f(L)}` is
the hypograph of `π_L`, and `D_L` is concave and piecewise affine on `ℝ²`." Here the first part, by
`{θ : D_L(α, θ) ≥ f(L)} = (−∞, π_L(α)]` (`Stoc.setOf_le_Dfun_eq`); `T_L` has no point above a share
`α` with `π_L(α) = −∞`. The second part is the setup's `Stoc.concaveOn_Dfun` and
`Stoc.pwAffine_Dfun`. -/
theorem Tset_eq (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) :
    Tset 𝓚 W f m β L = {p | ¬ PiBot 𝓚 W f m β L p.1 ∧ p.2 ≤ pressure 𝓚 W f m β L p.1} := by
  ext p
  constructor
  · intro hp
    have hgood : ¬ PiBot 𝓚 W f m β L p.1 := fun hbot =>
      absurd (hp : f L ≤ _) (not_le.2 (hbot p.2))
    have hmem : p.2 ∈ {θ | f L ≤ Dfun 𝓚 W f m β L p.1 θ} := hp
    rw [setOf_le_Dfun_eq h𝓚 hβ hL hLW hgood] at hmem
    exact ⟨hgood, hmem⟩
  · rintro ⟨hgood, hle⟩
    have hmem : p.2 ∈ Set.Iic (pressure 𝓚 W f m β L p.1) := hle
    rw [← setOf_le_Dfun_eq h𝓚 hβ hL hLW hgood] at hmem
    exact hmem

/-- Step (1) for `π_L ≢ −∞`: `T_L = {(α, θ) | θ ≤ π_L(α)}`, as `π_L(α) > −∞` for every `α`. -/
theorem Tset_eq_of_good (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) :
    Tset 𝓚 W f m β L = {p | p.2 ≤ pressure 𝓚 W f m β L p.1} := by
  rw [Tset_eq h𝓚 hβ hL hLW]
  ext p
  simp only [Set.mem_ofPred_eq, not_piBot_of_not_forall h𝓚 hβ hL hLW hgood p.1,
    not_false_eq_true, true_and]

/-- `T_L` is closed, as `D_L` is continuous (not in the paper: the proof uses it without saying
so). -/
theorem isClosed_Tset (h𝓚 : IsLaminar 𝓚) {L : Finset E} (hL : L ∈ 𝓚) :
    IsClosed (Tset 𝓚 W f m β L) :=
  isClosed_le continuous_const (continuous_Dfun h𝓚 hL)

/-- (Not in the paper: step (3) of `lem:E-piececount` uses without proof that the graph of `π_L`
lies on the boundary of its hypograph `T_L`.) The points `(α, π_L(α) + t)`, `t > 0`, lie outside
`T_L`. -/
theorem graph_mem_frontier (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) (α : ℝ) :
    (α, pressure 𝓚 W f m β L α) ∈ frontier (Tset 𝓚 W f m β L) := by
  rw [Tset_eq_of_good h𝓚 hβ hL hLW hgood]
  refine ⟨subset_closure (show pressure 𝓚 W f m β L α ≤ pressure 𝓚 W f m β L α from le_rfl),
    fun hint => ?_⟩
  have hlim : Tendsto (fun t : ℝ => (α, pressure 𝓚 W f m β L α + t)) (𝓝 0)
      (𝓝 (α, pressure 𝓚 W f m β L α)) := by
    have := ((by fun_prop : Continuous fun t : ℝ => (α, pressure 𝓚 W f m β L α + t))).tendsto 0
    simpa using this
  have hev := hlim.eventually (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨t, ht, ht0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have h1 : pressure 𝓚 W f m β L α + t ≤ pressure 𝓚 W f m β L α := ht
  have h2 : (0 : ℝ) < t := ht0
  linarith

/-- (Not in the paper: step (3) of `lem:E-piececount` uses without proof that a point of `∂T_J`
lies on the graph of `π_J`, "`z ∈ ∂T_J` …, that is, `z` lies on the graph of `π_J`.") The
boundary of `T_J` is empty if `π_J ≡ −∞`, and otherwise lies on the graph of the continuous
`π_J`. -/
theorem frontier_Tset_subset (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {J : Finset E} (hJ : J ∈ 𝓚)
    (hJW : (J ∩ W).Nonempty) {p : ℝ × ℝ} (hp : p ∈ frontier (Tset 𝓚 W f m β J)) :
    ¬ (∀ α, PiBot 𝓚 W f m β J α) ∧ p.2 = pressure 𝓚 W f m β J p.1 := by
  by_cases hbot : ∀ α, PiBot 𝓚 W f m β J α
  · have hempty : Tset 𝓚 W f m β J = ∅ := Set.eq_empty_of_forall_notMem fun q hq =>
      absurd (hq : f J ≤ _) (not_le.2 (hbot q.1 q.2))
    rw [hempty, frontier_empty] at hp
    exact absurd hp (Set.notMem_empty p)
  · rw [Tset_eq_of_good h𝓚 hβ hJ hJW hbot] at hp
    exact ⟨hbot, frontier_le_subset_eq continuous_snd
      ((continuous_pressure h𝓚 hβ hJ hJW hbot).comp continuous_fst) hp⟩

/-! ### Step (2): the points near which `D_L` is not affine -/

/-- **Step (2)** (`appB-quadratic.tex:846-849`): "Near interior points of `T_K` the function
`min {f(K), D_K}` equals `f(K)`, and near points outside `T_K` it equals `D_K`. So
`brk(min {f(K), D_K}) ⊆ ∂T_K ∪ brk(D_K)`." -/
theorem brk_min_subset (h𝓚 : IsLaminar 𝓚) {K : Finset E} (hK : K ∈ 𝓚) :
    brk (fun p => min (f K) (Dfun 𝓚 W f m β K p.1 p.2)) ⊆
      frontier (Tset 𝓚 W f m β K) ∪ brk (fun p => Dfun 𝓚 W f m β K p.1 p.2) := by
  intro p hp
  by_contra hno
  rw [Set.mem_union, not_or] at hno
  obtain ⟨hfr, hbrk⟩ := hno
  apply hp
  by_cases hint : p ∈ interior (Tset 𝓚 W f m β K)
  · -- "Near interior points of `T_K` the function `min {f(K), D_K}` equals `f(K)`, …"
    refine ⟨f K, 0, 0, ?_⟩
    filter_upwards [mem_interior_iff_mem_nhds.1 hint] with q hq
    rw [min_eq_left hq]
    ring
  · -- "… and near points outside `T_K` it equals `D_K`." Otherwise `p ∉ T_K`.
    have hnot : p ∉ Tset 𝓚 W f m β K := fun hT => hfr ⟨subset_closure hT, hint⟩
    obtain ⟨a, b, c, hev⟩ := not_not.1 hbrk
    refine ⟨a, b, c, ?_⟩
    filter_upwards [hev, (isClosed_Tset h𝓚 hK).isOpen_compl.mem_nhds hnot] with q hq hq'
    have hlt : Dfun 𝓚 W f m β K q.1 q.2 < f K := lt_of_not_ge hq'
    rw [min_eq_right hlt.le, hq]

/-- **Step (2)** (`appB-quadratic.tex:850-851`): "By (`eq:E-D`), `brk(D_L)` is contained in the
union of the sets `brk(min {f(K), D_K})` over the children `K` of `L`, …" -/
theorem brk_D_subset_children {L : Finset E} :
    brk (fun p => Dfun 𝓚 W f m β L p.1 p.2) ⊆
      ⋃ K ∈ children 𝓚 L, brk (fun p => min (f K) (Dfun 𝓚 W f m β K p.1 p.2)) := by
  intro p hp
  by_contra hno
  apply hp
  simp only [Set.mem_iUnion, not_exists] at hno
  have hK : ∀ K ∈ children 𝓚 L, ∃ a b c : ℝ, ∀ᶠ q in 𝓝 p,
      min (f K) (Dfun 𝓚 W f m β K q.1 q.2) = a + b * q.1 + c * q.2 := fun K hK =>
    not_not.1 (hno K hK)
  choose! a b c hK using hK
  refine ⟨∑ K ∈ children 𝓚 L, a K, tA m β (own 𝓚 W L) + ∑ K ∈ children 𝓚 L, b K,
    -binv β (own 𝓚 W L) + ∑ K ∈ children 𝓚 L, c K, ?_⟩
  filter_upwards [(eventually_all_finset _).2 hK] with q hq
  have hown : ∑ e ∈ own 𝓚 W L, (q.1 * m e - q.2) / β e =
      q.1 * tA m β (own 𝓚 W L) - q.2 * binv β (own 𝓚 W L) := by
    simp only [tA, binv, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  rw [Dfun_eq, sum_congr rfl hq, sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, hown]
  ring

/-- **Step (2)** (`appB-quadratic.tex:852`): "… and by induction `brk(D_L) ⊆ ⋃_{J⊊L} ∂T_J`."
The induction is over the forest. -/
theorem brk_D_subset (h𝓚 : IsLaminar 𝓚) :
    ∀ L ∈ 𝓚, brk (fun p => Dfun 𝓚 W f m β L p.1 p.2) ⊆
      ⋃ J ∈ 𝓚.filter (· ⊂ L), frontier (Tset 𝓚 W f m β J) := by
  intro L
  induction L using Finset.strongInduction with
  | H L ih =>
  intro hL p hp
  obtain ⟨K, hK, hpK⟩ := Set.mem_iUnion₂.1 (brk_D_subset_children hp)
  have hKL := ssubset_of_mem_children hK
  have hK𝓚 := (mem_children.1 hK).1
  rcases brk_min_subset h𝓚 hK𝓚 hpK with h | h
  · exact Set.mem_biUnion (mem_filter.2 ⟨hK𝓚, hKL⟩) h
  · obtain ⟨J, hJ, hJp⟩ := Set.mem_iUnion₂.1 (ih K hKL hK𝓚 h)
    exact Set.mem_biUnion (mem_filter.2 ⟨(mem_filter.1 hJ).1, (mem_filter.1 hJ).2.trans hKL⟩) hJp

/-! ### Step (3): the vertices of the graph of `π_L` -/

/-- **Step (3)** (`appB-quadratic.tex:854-858`): "Let `z` be a vertex of the graph of `π_L`. Then
`D_L(z) = f(L)`, and `D_L` is not affine near `z`. Otherwise, near `z`, the set `T_L` would be a
half-plane bounded by a line through `z`, or a whole neighborhood of `z`, and in neither case would
`z` be a vertex of the graph of `π_L`. So `z ∈ ∂T_J` for some `J ⊊ L`, that is, `z` lies on the
graph of `π_J`." Here `z = (α₀, π_L(α₀))`. A whole neighborhood of `z` would make `z` an interior
point of the hypograph `T_L`, but it lies on the graph of `π_L`; as `T_L` is a hypograph, the line
of a half-plane is not vertical, and near `z` the graph of `π_L` is this line. -/
theorem exists_eq_of_mem_kinks (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e)
    (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty) {L : Finset E} (hL : L ∈ 𝓚)
    (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) {α₀ : ℝ} (hk : α₀ ∈ kinks (pressure 𝓚 W f m β L)) :
    ∃ J ∈ 𝓚, J ⊂ L ∧ ¬ (∀ α, PiBot 𝓚 W f m β J α) ∧
      pressure 𝓚 W f m β J α₀ = pressure 𝓚 W f m β L α₀ := by
  have hLW := hmeet L hL
  set πL := pressure 𝓚 W f m β L
  set z : ℝ × ℝ := (α₀, πL α₀) with hz
  -- `T_L` is the hypograph of `π_L` (step (1))
  have hhyp : ∀ q : ℝ × ℝ, q ∈ Tset 𝓚 W f m β L ↔ q.2 ≤ πL q.1 := fun q => by
    rw [Tset_eq_of_good h𝓚 hβ hL hLW hgood]
    rfl
  -- (3) "Let `z` be a vertex of the graph of `π_L`. Then `D_L(z) = f(L)`, …"
  have hDz : Dfun 𝓚 W f m β L z.1 z.2 = f L :=
    Dfun_pressure h𝓚 hβ hL hLW (not_piBot_of_not_forall h𝓚 hβ hL hLW hgood α₀)
  -- (3) "… and `D_L` is not affine near `z`."
  have hbrk : z ∈ brk (fun p => Dfun 𝓚 W f m β L p.1 p.2) := by
    rintro ⟨a₁, b, c, hev⟩
    -- near `z`, `D_L − f(L) = a + b α + c θ` with `a = a₁ − f(L)`, and `a + b α₀ + c π_L(α₀) = 0`
    set a := a₁ - f L
    have hz0 : a + b * α₀ + c * πL α₀ = 0 := by
      have h := hev.self_of_nhds
      simp only at h
      simp only [a]
      linarith
    -- (3) "Otherwise, near `z`, the set `T_L` would be a half-plane bounded by a line through
    -- `z`, or a whole neighborhood of `z`, …"
    -- Near `z`, `T_L` is `{(α, θ) | a + b α + c θ ≥ 0}`, with the line `a + b α + c θ = 0`.
    have hT : ∀ᶠ q in 𝓝 z, (q ∈ Tset 𝓚 W f m β L ↔ 0 ≤ a + b * q.1 + c * q.2) :=
      hev.mono fun q hq => by
        have hq' : Dfun 𝓚 W f m β L q.1 q.2 = a₁ + b * q.1 + c * q.2 := hq
        show f L ≤ Dfun 𝓚 W f m β L q.1 q.2 ↔ _
        rw [hq']
        simp only [a]
        constructor <;> intro h <;> linarith
    by_cases hbc : b = 0 ∧ c = 0
    · -- (3) "… and in neither case would `z` be a vertex of the graph of `π_L`."
      -- A whole neighborhood of `z` would make `z` an interior point of `T_L`, but it lies on the
      -- graph of `π_L`.
      have hsub : ∀ᶠ q in 𝓝 z, q ∈ Tset 𝓚 W f m β L := hT.mono fun q hq => by
        rw [hq, hbc.1, hbc.2]
        rw [hbc.1, hbc.2] at hz0
        linarith
      exact (graph_mem_frontier h𝓚 hβ hL hLW hgood α₀).2 (mem_interior_iff_mem_nhds.2 hsub)
    · -- A half-plane: its line is not vertical, and near `z` the graph of `π_L` is the line.
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hT
      have hdist : ∀ x y : ℝ, |x - α₀| < δ → |y - πL α₀| < δ → dist (x, y) z < δ :=
        fun x y hx hy => by
          rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
          exact max_lt hx hy
      -- the points directly above `z` lie outside the hypograph `T_L`, so `c < 0`
      have hc : c < 0 := by
        have hq := hdist α₀ (πL α₀ + δ / 2) (by rw [sub_self, abs_zero]; exact hδ)
          (by rw [add_sub_cancel_left, abs_of_pos (half_pos hδ)]; linarith)
        have hout : (α₀, πL α₀ + δ / 2) ∉ Tset 𝓚 W f m β L := fun h => by
          have := (hhyp _).1 h
          simp only at this
          linarith
        have hlt : a + b * α₀ + c * (πL α₀ + δ / 2) < 0 :=
          lt_of_not_ge fun h => hout ((hball hq).2 h)
        nlinarith
      have hc0 : c ≠ 0 := hc.ne
      -- near `α₀`, the graph of `π_L` is the line `π_L(α) = −(a + b α)/c`, so `z` is no vertex
      obtain ⟨η, hη, hηball⟩ := Metric.continuousAt_iff.1
        (continuous_pressure h𝓚 hβ hL hLW hgood).continuousAt (δ / 2) (half_pos hδ)
      apply hk
      refine ⟨min η (δ / 2), lt_min hη (half_pos hδ), -a / c, -b / c, fun α hα => ?_⟩
      have hαε : |α - α₀| < min η (δ / 2) :=
        abs_sub_lt_iff.2 ⟨by linarith [hα.2], by linarith [hα.1]⟩
      have hα1 : |α - α₀| < δ / 2 := hαε.trans_le (min_le_right _ _)
      have hα2 : |πL α - πL α₀| < δ / 2 := by
        have := hηball (show dist α α₀ < η by
          rw [Real.dist_eq]
          exact hαε.trans_le (min_le_left _ _))
        rwa [Real.dist_eq] at this
      -- for `θ` near `π_L(α)`, `(α, θ)` lies in `T_L` iff it lies in the half-plane
      have hloc : ∀ θ, |θ - πL α| < δ / 2 → (θ ≤ πL α ↔ 0 ≤ a + b * α + c * θ) := fun θ hθ =>
        (hhyp (α, θ)).symm.trans (hball (hdist α θ (by linarith)
          (by
            calc |θ - πL α₀| = |(θ - πL α) + (πL α - πL α₀)| := by rw [sub_add_sub_cancel]
              _ ≤ |θ - πL α| + |πL α - πL α₀| := abs_add_le _ _
              _ < δ := by linarith)))
      have h0 : a + b * α + c * πL α = 0 := by
        refine le_antisymm ?_ ((hloc (πL α) (by rw [sub_self, abs_zero]; linarith)).1 le_rfl)
        by_contra hpos
        push Not at hpos
        set s := a + b * α + c * πL α
        set t := min (δ / 4) (s / (-2 * c))
        have ht : 0 < t := lt_min (by linarith) (div_pos hpos (by linarith))
        have ht1 : t ≤ δ / 4 := min_le_left _ _
        have hct : -(s / 2) ≤ c * t := by
          have h1 : c * (s / (-2 * c)) = -(s / 2) := by
            field_simp
          have h2 := mul_le_mul_of_nonpos_left (min_le_right (δ / 4) (s / (-2 * c))) hc.le
          linarith
        have hin := (hloc (πL α + t) (by rw [add_sub_cancel_left, abs_of_pos ht]; linarith)).2
          (by linarith)
        linarith
      field_simp
      linarith
  -- (3) "So `z ∈ ∂T_J` for some `J ⊊ L`, that is, `z` lies on the graph of `π_J`." (step (2),
  -- `brk_D_subset`)
  obtain ⟨J, hJ, hzJ⟩ := Set.mem_iUnion₂.1 (brk_D_subset h𝓚 L hL hbrk)
  obtain ⟨hJ𝓚, hJL⟩ := mem_filter.1 hJ
  obtain ⟨hJgood, hJz⟩ := frontier_Tset_subset h𝓚 hβ hJ𝓚 (hmeet J hJ𝓚) hzJ
  exact ⟨J, hJ𝓚, hJL, hJgood, hJz.symm⟩

/-! ### Step (4): at most two vertices on a linear piece -/

/-- **Step (4)** (`appB-quadratic.tex:858-863`): "Now let `γ` be a linear piece of the graph of some
`π_J`, over a closed interval `O`. On `O`, the function `π_L − π_J` is concave, so its zero set in
`O` consists of at most two points or is an interval, on whose interior `π_L = π_J` is affine.
Hence `γ` contains at most two vertices of the graph of `π_L`." Here `O` is a linear piece of
`π_J` (`Stoc.linPieces`), on which `π_J` is affine, and the zero set is that of
`Stoc.zeroSet_finite_or_ordConnected_of_concaveOn`. The vertices on `γ` are counted by their first
coordinates: the kinks `α ∈ O` of `π_L` with `π_L(α) = π_J(α)`; they lie in the zero set but not
in its interior, so if it is an interval, they are among its at most two boundary points
(`Stoc.finite_ncard_diff_interior_le_two`). -/
theorem ncard_vertices_le_two (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L J : Finset E}
    (hL : L ∈ 𝓚) (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) (hJ : J ∈ 𝓚)
    (hJW : (J ∩ W).Nonempty) (hJgood : ¬ ∀ α, PiBot 𝓚 W f m β J α) {O : Set ℝ}
    (hO : O ∈ linPieces (pressure 𝓚 W f m β J)) :
    {α ∈ O | α ∈ kinks (pressure 𝓚 W f m β L) ∧
        pressure 𝓚 W f m β L α = pressure 𝓚 W f m β J α}.Finite ∧
      {α ∈ O | α ∈ kinks (pressure 𝓚 W f m β L) ∧
        pressure 𝓚 W f m β L α = pressure 𝓚 W f m β J α}.ncard ≤ 2 := by
  set πL := pressure 𝓚 W f m β L
  set πJ := pressure 𝓚 W f m β J
  -- (4) "Now let `γ` be a linear piece of the graph of some `π_J`, over a closed interval `O`."
  -- So `π_J` is affine on `O`.
  obtain ⟨c, d, hcd⟩ := exists_affine_of_mem_linPieces (kinks_pressure_finite h𝓚 hβ hJ hJW hJgood)
    (continuous_pressure h𝓚 hβ hJ hJW hJgood) hO
  replace hcd : ∀ α ∈ O, πJ α = c + d * α := hcd
  have hOc : O.OrdConnected := ordConnected_of_mem_linPieces hO
  -- (4) "On `O`, the function `π_L − π_J` is concave, …"
  have hconc : ConcaveOn ℝ O fun α => πL α - πJ α := by
    have hπL := concaveOn_pressure h𝓚 hβ hL hLW hgood
    refine ⟨hOc.convex, fun x hx y hy a b ha hb hab => ?_⟩
    have hxy : a • x + b • y ∈ O := hOc.convex hx hy ha hb hab
    have hφ := hπL.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at hxy hφ ⊢
    rw [hcd _ hxy, hcd x hx, hcd y hy]
    have heq : c + d * (a * x + b * y) = a * (c + d * x) + b * (c + d * y) := by
      linear_combination (-c) * hab
    have e1 : a * (πL x - (c + d * x)) + b * (πL y - (c + d * y)) =
        (a * πL x + b * πL y) - (a * (c + d * x) + b * (c + d * y)) := by ring
    linarith
  -- (4) "… so its zero set in `O` consists of at most two points or is an interval, …"
  -- The vertices on `γ` are zeros of `π_L − π_J`.
  set Z := {α ∈ O | πL α - πJ α = 0}
  set V := {α ∈ O | α ∈ kinks πL ∧ πL α = πJ α}
  have hVZ : V ⊆ Z := fun α hα => ⟨hα.1, sub_eq_zero.2 hα.2.2⟩
  -- (4) "… on whose interior `π_L = π_J` is affine."
  -- So no vertex lies in the interior.
  have hVint : ∀ α ∈ V, α ∉ interior Z := by
    intro α hα hint
    apply hα.2.1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    refine ⟨ε, hε, c, d, fun α' hα' => ?_⟩
    have hα'Z : α' ∈ Z := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hα'.1, hα'.2])
    rw [sub_eq_zero.1 hα'Z.2, hcd α' hα'Z.1]
  -- (4) "Hence `γ` contains at most two vertices of the graph of `π_L`."
  rcases zeroSet_finite_or_ordConnected_of_concaveOn hconc with ⟨hZfin, hZcard⟩ | hZc
  · exact ⟨hZfin.subset hVZ, (Set.ncard_le_ncard hVZ hZfin).trans hZcard⟩
  · exact finite_ncard_diff_interior_le_two hZc fun α hα => ⟨hVZ hα, hVint α hα⟩

/-! ### Step (5): the first inequality -/

/-- A union of the sets `V P` over a finite set `Ps` of linear pieces, each with at most `k`
points, has at most `k |Ps|` points. -/
theorem finite_ncard_biUnion_set_le {Ps : Set (Set ℝ)} (hPs : Ps.Finite) (V : Set ℝ → Set ℝ)
    (k : ℕ) (hV : ∀ P ∈ Ps, (V P).Finite ∧ (V P).ncard ≤ k) :
    (⋃ P ∈ Ps, V P).Finite ∧ (⋃ P ∈ Ps, V P).ncard ≤ k * Ps.ncard := by
  classical
  have h := finite_ncard_biUnion_le hPs.toFinset V (fun _ => k)
    fun P hP => hV P (hPs.mem_toFinset.1 hP)
  have heq : (⋃ P ∈ hPs.toFinset, V P) = ⋃ P ∈ Ps, V P := by
    ext x
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
  rw [heq, sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hPs, mul_comm] at h
  exact h

/-- **Step (5)** (`appB-quadratic.tex:863-864`): "… this graph has `#(L) − 1` vertices …", as
`π_L ≢ −∞` is piecewise linear (`Stoc.kinks_pressure_finite`) with `|kinks π_L| + 1` linear pieces
(`Stoc.linPieces_finite_ncard`). -/
theorem numPieces_eq (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) :
    numPieces 𝓚 W f m β L = (kinks (pressure 𝓚 W f m β L)).ncard + 1 := by
  rw [numPieces, ite_eq_right hgood]
  exact (linPieces_finite_ncard (kinks_pressure_finite h𝓚 hβ hL hLW hgood)).2

/-- **`lem:E-piececount`**, first inequality (`appB-quadratic.tex:835-841`, proof `:843-874`): for
`L ∈ 𝓛_W`, `#(L) ≤ 1 + 2 ∑_{J ⊊ L} #(J)`. Every vertex of the graph of `π_L` lies on the graph of
some `π_J`, `J ⊊ L` (step (3), `exists_eq_of_mem_kinks`), hence on one of its `#(J)` linear pieces
(`Stoc.exists_mem_linPieces`), and each of these carries at most two vertices (step (4),
`ncard_vertices_le_two`); as the graph of `π_L` has `#(L) − 1` vertices (step (5),
`numPieces_eq`), the inequality follows. -/
theorem numPieces_le (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty)
    {L : Finset E} (hL : L ∈ 𝓚) :
    numPieces 𝓚 W f m β L ≤ 1 + 2 * ∑ J ∈ 𝓚.filter (· ⊂ L), numPieces 𝓚 W f m β J := by
  classical
  by_cases hbad : ∀ α, PiBot 𝓚 W f m β L α
  · rw [numPieces, ite_eq_left hbad]
    omega
  have hLW := hmeet L hL
  -- the constraint sets `J ⊊ L` with `π_J ≢ −∞`, and the vertices of `π_L` on a linear piece `O`
  -- of `π_J`
  set G := 𝓚.filter fun J => J ⊂ L ∧ ¬ ∀ α, PiBot 𝓚 W f m β J α
  set V : Finset E → Set ℝ → Set ℝ := fun J O => {α ∈ O | α ∈ kinks (pressure 𝓚 W f m β L) ∧
    pressure 𝓚 W f m β L α = pressure 𝓚 W f m β J α}
  -- (3) "So `z ∈ ∂T_J` for some `J ⊊ L`, that is, `z` lies on the graph of `π_J`."
  -- So every vertex of the graph of `π_L` lies on one of the linear pieces of such a `π_J`.
  have hsub : kinks (pressure 𝓚 W f m β L) ⊆
      ⋃ J ∈ G, ⋃ O ∈ linPieces (pressure 𝓚 W f m β J), V J O := by
    intro α hα
    obtain ⟨J, hJ𝓚, hJL, hJgood, hJα⟩ := exists_eq_of_mem_kinks h𝓚 hβ hmeet hL hbad hα
    obtain ⟨O, hO, hαO⟩ :=
      exists_mem_linPieces (kinks_pressure_finite h𝓚 hβ hJ𝓚 (hmeet J hJ𝓚) hJgood) α
    exact Set.mem_biUnion (mem_filter.2 ⟨hJ𝓚, hJL, hJgood⟩)
      (Set.mem_biUnion hO ⟨hαO, hα, hJα.symm⟩)
  -- (4) "Hence `γ` contains at most two vertices of the graph of `π_L`."
  -- So the `#(J)` linear pieces of the graph of `π_J` carry at most `2#(J)` of them.
  have hU : ∀ J ∈ G, (⋃ O ∈ linPieces (pressure 𝓚 W f m β J), V J O).Finite ∧
      (⋃ O ∈ linPieces (pressure 𝓚 W f m β J), V J O).ncard ≤ 2 * numPieces 𝓚 W f m β J := by
    intro J hJ
    obtain ⟨hJ𝓚, -, hJgood⟩ := mem_filter.1 hJ
    have hfin := (linPieces_finite_ncard
      (kinks_pressure_finite h𝓚 hβ hJ𝓚 (hmeet J hJ𝓚) hJgood)).1
    rw [numPieces, ite_eq_right hJgood]
    exact finite_ncard_biUnion_set_le hfin (V J) 2 fun O hO =>
      ncard_vertices_le_two h𝓚 hβ hL hLW hbad hJ𝓚 (hmeet J hJ𝓚) hJgood hO
  obtain ⟨hfinU, hcardU⟩ := finite_ncard_biUnion_le G
    (fun J => ⋃ O ∈ linPieces (pressure 𝓚 W f m β J), V J O)
    (fun J => 2 * numPieces 𝓚 W f m β J) hU
  have hk : (kinks (pressure 𝓚 W f m β L)).ncard ≤
      2 * ∑ J ∈ 𝓚.filter (· ⊂ L), numPieces 𝓚 W f m β J := by
    refine (Set.ncard_le_ncard hsub hfinU).trans (hcardU.trans ?_)
    rw [← mul_sum]
    exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset fun J hJ =>
      mem_filter.2 ⟨(mem_filter.1 hJ).1, (mem_filter.1 hJ).2.1⟩)
  -- (5) "As this graph has `#(L) − 1` vertices, the first inequality follows."
  rw [numPieces_eq h𝓚 hβ hL hLW hbad]
  omega

end

end Stoc
