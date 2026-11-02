-- stamp r9 2026-11-02
import Stoc.Hardness.Operations
import Stoc.Hardness.Splice
import Stoc.OptimalShare.Exponential

/-!
# Cut forms

The STOC version's `def:cutform` and `lem:cutforms` (Appendix C.2, `sec:D-cutforms`, "Cut forms",
`stoc-sections/appD-hardness.tex:98-151`).

* `CutForm`, `CutForm.cut`, `CutForm.fn`: `def:cutform`. A cut form on `E` is a loopless digraph
  `D` on `E` (a finite set of arcs `(u, v)` with `u ≠ v`), capacities `cap ≥ 0` on its arcs and
  weights `ω`, and defines `f(S) = cut_D(S) + ω(S)` (`eq:cutform`), where `cut_D(S)` is the total
  capacity of the arcs that leave `S`. `HasCutForm f`: `f` is given by a cut form. `Ccut`: the
  class `𝒞_cut` of instances `(f, m, β)` with `m, β > 0` for which `f` is a polymatroid rank
  function given by a cut form.
* `cutforms_a`: `lem:cutforms`(a), every function given by a cut form is submodular, by the
  argument after "Indeed" in the proof (the paper also cites `[Sch03, (44.16)]` for it), with the
  D3 lemma `submodular_sum` (a sum of submodular functions is submodular).
* `cutforms_b`: `lem:cutforms`(b), the cut form defines a polymatroid rank function if and only
  if every weight `ω_e` is at least the total capacity of the arcs entering `e`.
* `cutforms_c`: `lem:cutforms`(c), with the forms of its parts (i)-(iii) and of the disjoint
  union (`CutForm.addModular`, `CutForm.addNode`, `CutForm.extendForm`, `CutForm.dsumForm`).
* `cutforms`: the statement of `lem:cutforms`, the conjunction of (a)–(c), proved by the three
  parts.
* `translation_a_cutForm`: `lem:translation`(a) with its sentence on cut forms
  (`lem:cutforms`(c)(iii)); `translation`: the statement of `lem:translation`, the conjunction of
  (a)–(c), with (b) and (c) from `Stoc/Hardness/Translation.lean`. Both need `lem:cutforms` and so
  come in this file.

The data of the paper are rational and encoded in binary; here they are real numbers. The bit
model is in `Stoc/Hardness/Encoding.lean`: instances with rational data (`RatInst`), their encoding
length `⟨I⟩`, and the recognition of `𝒞_cut` in `lem:cutforms`(b) (`RatInst.inCcut_iff`).

Taken over on 2026-10-20 from `Paper/Hardness/CutForms.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### `def:cutform` -/

/-- A cut form on `E` (`def:cutform`, Definition C.2, `stoc-sections/appD-hardness.tex:98-104`):
a loopless digraph `D` on `E`, given by its finite set of arcs `(u, v)` with `u ≠ v`, capacities
`cap(u, v) ≥ 0` on the arcs of `D` (the values of `cap` off `D` play no role) and weights `ω`. The
STOC version takes rational capacities and weights; here they are real. -/
structure CutForm (E : Type*) where
  /-- the arcs of the digraph -/
  D : Finset (E × E)
  /-- the digraph has no loops -/
  loopless : ∀ a ∈ D, a.1 ≠ a.2
  /-- the capacities -/
  cap : E × E → ℝ
  cap_nonneg : ∀ a ∈ D, 0 ≤ cap a
  /-- the weights -/
  ω : E → ℝ

namespace CutForm

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `cut_D(S) = ∑_{(u, v) ∈ D : u ∈ S, v ∉ S} cap(u, v)`, the total capacity of the arcs of `D`
that leave `S` (`eq:cutform`). -/
def cut (F : CutForm E) (S : Finset E) : ℝ :=
  ∑ a ∈ F.D with a.1 ∈ S ∧ a.2 ∉ S, F.cap a

/-- The function `f(S) = cut_D(S) + ω(S)` of a cut form (`eq:cutform`). -/
def fn (F : CutForm E) (S : Finset E) : ℝ :=
  F.cut S + ∑ e ∈ S, F.ω e

end CutForm

/-- `f` is given by a cut form: `f = cut_D + ω` for a cut form `(D, cap, ω)` (`def:cutform`). -/
def HasCutForm {E : Type*} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) : Prop :=
  ∃ F : CutForm E, ∀ S, f S = F.fn S

/-- The class `𝒞_cut` (`def:cutform`, `stoc-sections/appD-hardness.tex:103`): instances
`(f, m, β)` with `m, β > 0` for which `f` is a polymatroid rank function given by a cut form.
The STOC version asks for rational `m`, `β` and a rational cut form, all encoded in binary; the
rational data and their encoding length are `RatInst` and `RatInst.encI` in
`Stoc/Hardness/Encoding.lean`, and `RatInst.InCcut` is this class for them. -/
structure Ccut {E : Type*} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (m β : E → ℝ) :
    Prop where
  m_pos : ∀ e, 0 < m e
  β_pos : ∀ e, 0 < β e
  rank : IsRankFunction f
  cutForm : HasCutForm f

/-! ### `lem:cutforms`(a) -/

section PartA

variable {E : Type*} [DecidableEq E]

/-- The contribution of one arc `(u, v)` of capacity `c` to `cut_D(S)`: `c` if `u ∈ S` and
`v ∉ S`, and nothing otherwise. -/
def arcCut (c : ℝ) (u v : E) (S : Finset E) : ℝ :=
  if u ∈ S ∧ v ∉ S then c else 0

/-- The marginal values in the contribution of an arc `(u, v)` with `u ≠ v`: that of `u` at a set
`S ∌ u` is `c` if `v ∉ S` and `0` otherwise, that of `v` at a set `S ∌ v` is `−c` if `u ∈ S` and
`0` otherwise, and that of every other element is `0`. -/
lemma arcCut_marginal {c : ℝ} {u v : E} (huv : u ≠ v) {S : Finset E} {e : E} (he : e ∉ S) :
    arcCut c u v (insert e S) - arcCut c u v S =
      if e = u then (if v ∉ S then c else 0)
      else if e = v then (if u ∈ S then -c else 0) else 0 := by
  unfold arcCut
  by_cases heu : e = u
  · subst heu
    have hv : v ≠ e := huv.symm
    simp [he, hv]
  · by_cases hev : e = v
    · subst hev
      by_cases hu : u ∈ S <;> simp [he, heu, Ne.symm heu, hu]
    · simp [heu, hev, Ne.symm heu, Ne.symm hev]

/-- The contribution of an arc with nonnegative capacity is submodular, as its marginal values
are nonincreasing in `S` (diminishing returns). -/
lemma arcCut_submodular {c : ℝ} (hc : 0 ≤ c) {u v : E} (huv : u ≠ v) :
    Submodular (arcCut c u v) := by
  refine DiminishingReturns.submodular fun X Y e hXY heY => ?_
  have heX : e ∉ X := fun h => heY (hXY h)
  rw [arcCut_marginal huv heY, arcCut_marginal huv heX]
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- A sum of submodular functions is submodular (not in the paper: the proof of `lem:cutforms`(a)
uses "and so is their sum `cut_D`" without proof). -/
lemma submodular_sum {ι : Type*} (s : Finset ι) {g : ι → Finset E → ℝ}
    (hg : ∀ i ∈ s, Submodular (g i)) : Submodular fun S => ∑ i ∈ s, g i S := by
  intro X Y
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact sum_le_sum fun i hi => hg i hi X Y

end PartA

/-- **`lem:cutforms`(a)** (Lemma C.3, `stoc-sections/appD-hardness.tex:108`, proof lines 130-133):
every function given by a cut form is submodular.

The proof's steps: (1) a directed cut function with nonnegative capacities is submodular (the
paper cites `[Sch03, (44.16)]`, "as used in the proof of `thm:alm`", and proves it after "Indeed",
which the Lean follows): each arc `(u, v)` contributes `cap(u, v)` to `cut_D(S)` if `u ∈ S` and
`v ∉ S` and nothing otherwise; in this contribution the marginal values of `u`, of `v` and of the
other elements are nonincreasing in `S`, as `cap(u, v) ≥ 0`, so each contribution is submodular
(`arcCut_submodular`), and so is their sum `cut_D` (`submodular_sum`); (2) "and so is its sum with
a modular function". -/
theorem cutforms_a {E : Type*} [Fintype E] [DecidableEq E] (F : CutForm E) :
    Submodular F.fn := by
  -- (1) "A directed cut function with nonnegative capacities is submodular [Sch03, (44.16)], as
  -- used in the proof of `thm:alm`, … Indeed, each arc `(u, v) ∈ D` contributes `cap(u, v)` to
  -- `cut_D(S)` if `u ∈ S` and `v ∉ S`, and nothing otherwise. In this contribution, the marginal
  -- value of `u` at a set `S ∌ u` is `cap(u, v)` if `v ∉ S` and `0` otherwise, the marginal value
  -- of `v` at a set `S ∌ v` is `−cap(u, v)` if `u ∈ S` and `0` otherwise, and the marginal value
  -- of every other element is `0`. As `cap(u, v) ≥ 0`, all of them are nonincreasing in `S`, so
  -- each contribution is submodular, and so is their sum `cut_D`."
  have hcut : F.cut = fun S => ∑ a ∈ F.D, arcCut (F.cap a) a.1 a.2 S := by
    funext S
    rw [CutForm.cut, sum_filter]
    rfl
  have h1 : Submodular F.cut := by
    rw [hcut]
    exact submodular_sum F.D fun a ha => arcCut_submodular (F.cap_nonneg a ha) (F.loopless a ha)
  -- (2) "…, and so is its sum with a modular function."
  intro X Y
  have h2 : ∑ e ∈ X ∪ Y, F.ω e + ∑ e ∈ X ∩ Y, F.ω e = ∑ e ∈ X, F.ω e + ∑ e ∈ Y, F.ω e :=
    sum_union_inter
  have := h1 X Y
  unfold CutForm.fn
  linarith

/-! ### `lem:cutforms`(b) -/

section PartB

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The step of the proof of `lem:cutforms`(b): a submodular `f` with `f(∅) = 0` is monotone if
and only if `f(E) − f(E ∖ {e}) ≥ 0` for every `e ∈ E`, because
`f(S ∪ {e}) − f(S) ≥ f(E) − f(E ∖ {e})` for every `S ⊆ E ∖ {e}`. -/
theorem monotone_iff_top {f : Finset E → ℝ} (hs : Submodular f) :
    Monotone f ↔ ∀ e, 0 ≤ f univ - f (univ.erase e) := by
  constructor
  · intro hm e
    have := hm (erase_subset e univ)
    linarith
  · intro htop
    refine Exp.monotone_of_insert fun S e he => ?_
    have hdr := hs.diminishingReturns (X := S) (Y := univ.erase e) (e := e)
      (fun x hx => mem_erase.2 ⟨fun h => he (h ▸ hx), mem_univ x⟩) (notMem_erase e univ)
    rw [insert_erase (mem_univ e)] at hdr
    linarith [htop e]

/-- The step of the proof of `lem:cutforms`(b): no arc leaves `E`, and as `D` has no loops, the
arcs that leave `E ∖ {e}` are exactly those that enter `e`, so
`f(E) − f(E ∖ {e}) = ω_e − ∑_{(u, e) ∈ D} cap(u, e)`. -/
theorem CutForm.fn_top (F : CutForm E) (e : E) :
    F.fn univ - F.fn (univ.erase e) = F.ω e - ∑ a ∈ F.D with a.2 = e, F.cap a := by
  have h1 : F.cut univ = 0 := by
    unfold CutForm.cut
    simp
  have h2 : F.cut (univ.erase e) = ∑ a ∈ F.D with a.2 = e, F.cap a := by
    unfold CutForm.cut
    refine sum_congr ?_ fun _ _ => rfl
    ext a
    simp only [mem_filter, mem_erase, ne_eq, mem_univ, and_true, not_not]
    constructor
    · rintro ⟨ha, -, h⟩
      exact ⟨ha, h⟩
    · rintro ⟨ha, h⟩
      exact ⟨ha, fun h' => F.loopless a ha (h'.trans h.symm), h⟩
  have h3 : ∑ x ∈ univ, F.ω x - ∑ x ∈ univ.erase e, F.ω x = F.ω e := by
    rw [sum_erase_eq_sub (mem_univ e)]
    ring
  unfold CutForm.fn
  rw [h1, h2]
  linarith

/-- **`lem:cutforms`(b)** (`stoc-sections/appD-hardness.tex:109`, proof lines 135-141): the cut
form `(D, cap, ω)` defines a polymatroid rank function if and only if, for every `e ∈ E`, `ω_e`
is at least the total capacity of the arcs of `D` that enter `e`. (Its "in particular",
membership in `𝒞_cut` is decided in polynomial time, is `RatInst.inCcut_iff` for rational data.)

The proof's steps: (1) `f(∅) = 0`, and `f` is submodular by (a); (2) a submodular `f` with
`f(∅) = 0` is monotone if and only if `f(E) − f(E ∖ {e}) ≥ 0` for every `e`
(`monotone_iff_top`); (3) a monotone `f` with `f(∅) = 0` is nonnegative; (4) no arc leaves `E`,
and the arcs that leave `E ∖ {e}` are those that enter `e`, so `f(E) − f(E ∖ {e})` is `ω_e` minus
the capacity entering `e` (`CutForm.fn_top`); (5) the polynomial-time check
(`RatInst.inCcut_iff`). -/
theorem cutforms_b (F : CutForm E) :
    IsRankFunction F.fn ↔ ∀ e, ∑ a ∈ F.D with a.2 = e, F.cap a ≤ F.ω e := by
  -- (1) "Always `f(∅) = 0`, as `cut_D(∅) = 0`, and `f` is submodular by (a)."
  have h0 : F.fn ∅ = 0 := by simp [CutForm.fn, CutForm.cut]
  have hs := cutforms_a F
  -- (2) "A submodular `f` with `f(∅) = 0` is monotone if and only if `f(E) − f(E ∖ {e}) ≥ 0` for
  -- every `e ∈ E`, because `f(S ∪ {e}) − f(S) ≥ f(E) − f(E ∖ {e})` for every `S ⊆ E ∖ {e}`."
  have hmono := monotone_iff_top hs
  -- (3) "A monotone `f` with `f(∅) = 0` is nonnegative." (The rank functions of Section 2 are
  -- normalised, monotone and submodular; the equivalence does not use this.)
  have hnn : Monotone F.fn → ∀ S, 0 ≤ F.fn S := fun hm S => h0 ▸ hm (empty_subset S)
  -- (4) "No arc leaves `E`, and as `D` has no loops, the arcs that leave `E ∖ {e}` are exactly
  -- those that enter `e`. So `f(E) − f(E ∖ {e})` is `ω_e` minus the total capacity of the arcs
  -- entering `e`, which proves the equivalence."
  have htop := F.fn_top
  constructor
  · intro h e
    have := (hmono.1 h.mono) e
    rw [htop e] at this
    linarith
  · intro h
    refine ⟨h0, hmono.2 fun e => ?_, hs⟩
    rw [htop e]
    linarith [h e]

end PartB

/-! ### `lem:cutforms`(c) -/

section PartC

namespace CutForm

section

variable {E : Type*} [DecidableEq E]

/-- (c)(i): the form of `g` plus the modular function `S ↦ y(S)`, with `ω` replaced by `ω + y`. -/
def addModular (F : CutForm E) (y : E → ℝ) : CutForm E where
  D := F.D
  loopless := F.loopless
  cap := F.cap
  cap_nonneg := F.cap_nonneg
  ω e := F.ω e + y e

theorem fn_addModular (F : CutForm E) (y : E → ℝ) (S : Finset E) :
    (F.addModular y).fn S = F.fn S + ∑ e ∈ S, y e := by
  simp only [fn, cut, addModular, sum_add_distrib]
  ring

/-- The arcs of `D` on `Option E`: `(some u, some v)` for `(u, v) ∈ D`. -/
def someArcs (F : CutForm E) : Finset (Option E × Option E) :=
  F.D.map (Function.Embedding.some.prodMap Function.Embedding.some)

omit [DecidableEq E] in
lemma mem_someArcs {F : CutForm E} {a : Option E × Option E} :
    a ∈ F.someArcs ↔ ∃ u v, (u, v) ∈ F.D ∧ a = (some u, some v) := by
  simp only [someArcs, mem_map, Function.Embedding.prodMap, Function.Embedding.coeFn_mk,
    Prod.exists, Function.Embedding.some_apply]
  constructor
  · rintro ⟨u, v, h, rfl⟩
    exact ⟨u, v, h, rfl⟩
  · rintro ⟨u, v, h, rfl⟩
    exact ⟨u, v, h, rfl⟩

/-- The capacities on `Option E`: those of `D` on the old arcs, `d_e` on the arcs `none → some e`
(used by (iii)), and `0` elsewhere. -/
def optCap (F : CutForm E) (d : E → ℝ) : Option E × Option E → ℝ
  | (some u, some v) => F.cap (u, v)
  | (none, some v) => d v
  | _ => 0

/-- The arcs of `D` join nodes of `E`, so on `Option E` they contribute `cut_D(S)` to the cut of
every set `T` with `T ∩ E = S`. -/
lemma sum_someArcs (F : CutForm E) (d : E → ℝ) (T : Finset (Option E)) :
    ∑ a ∈ F.someArcs with a.1 ∈ T ∧ a.2 ∉ T, F.optCap d a = F.cut (eraseNone T) := by
  rw [someArcs, filter_map, sum_map, cut]
  refine sum_congr ?_ fun a _ => ?_
  · ext a
    simp [mem_eraseNone]
  · rcases a with ⟨u, v⟩
    rfl

/-- (c)(ii): the form of the direct sum `g ⊕ π_F` with a modular singleton `π_F` on a new
element `b` (here `none` in `Option E`): `b` is an isolated node of weight `F`. -/
def addNode (F : CutForm E) (Fb : ℝ) : CutForm (Option E) where
  D := F.someArcs
  loopless a ha := by
    obtain ⟨u, v, h, rfl⟩ := mem_someArcs.1 ha
    simpa using F.loopless _ h
  cap := F.optCap 0
  cap_nonneg a ha := by
    obtain ⟨u, v, h, rfl⟩ := mem_someArcs.1 ha
    exact F.cap_nonneg _ h
  ω o := Option.elim o Fb F.ω

end

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
/-- The arc `b → e` from the new node `b = none`. -/
def arcFromNone : E ↪ Option E × Option E :=
  ⟨fun e => (none, some e), fun _ _ h => by simpa using h⟩

omit [Fintype E] [DecidableEq E] in
@[simp] lemma arcFromNone_apply (e : E) : arcFromNone e = (none, some e) := rfl

/-- The arcs `b → e` of capacity `d_e` of the extension (iii), for every `e ∈ E`. -/
def newArcs : Finset (Option E × Option E) :=
  (univ : Finset E).map arcFromNone

omit [DecidableEq E] in
lemma disjoint_someArcs_newArcs (F : CutForm E) : Disjoint F.someArcs newArcs := by
  rw [disjoint_left]
  intro a ha ha'
  obtain ⟨u, v, -, rfl⟩ := mem_someArcs.1 ha
  obtain ⟨e, -, he⟩ := mem_map.1 ha'
  simp only [arcFromNone_apply, Prod.mk.injEq, reduceCtorEq, false_and] at he

/-- (c)(iii): the form of the one-element extension `g'` by `b` (here `none`) with `K` and
`d ≥ 0`: the node `b` with weight `K − d(E)` and the arcs `b → e` of capacity `d_e`. -/
def extendForm (F : CutForm E) {d : E → ℝ} (hd : ∀ e, 0 ≤ d e) (K : ℝ) : CutForm (Option E) where
  D := F.someArcs ∪ newArcs
  loopless a ha := by
    rcases mem_union.1 ha with ha | ha
    · obtain ⟨u, v, h, rfl⟩ := mem_someArcs.1 ha
      simpa using F.loopless _ h
    · obtain ⟨e, -, rfl⟩ := mem_map.1 ha
      simp only [arcFromNone_apply, ne_eq, reduceCtorEq, not_false_eq_true]
  cap := F.optCap d
  cap_nonneg a ha := by
    rcases mem_union.1 ha with ha | ha
    · obtain ⟨u, v, h, rfl⟩ := mem_someArcs.1 ha
      exact F.cap_nonneg _ h
    · obtain ⟨e, -, rfl⟩ := mem_map.1 ha
      exact hd e
  ω o := Option.elim o (K - ∑ e, d e) F.ω

omit [Fintype E] [DecidableEq E] in
/-- The disjoint union of two cut forms on `E₁` and `E₂`, on `E₁ ⊕ E₂`. -/
def dsumForm {E₁ E₂ : Type*} [DecidableEq E₁] [DecidableEq E₂] (F₁ : CutForm E₁)
    (F₂ : CutForm E₂) : CutForm (E₁ ⊕ E₂) where
  D := F₁.D.map (Function.Embedding.inl.prodMap Function.Embedding.inl) ∪
    F₂.D.map (Function.Embedding.inr.prodMap Function.Embedding.inr)
  loopless a ha := by
    simp only [mem_union, mem_map, Function.Embedding.prodMap, Function.Embedding.coeFn_mk,
      Prod.exists] at ha
    rcases ha with ⟨u, v, h, rfl⟩ | ⟨u, v, h, rfl⟩
    · simpa using F₁.loopless _ h
    · simpa using F₂.loopless _ h
  cap
    | (Sum.inl u, Sum.inl v) => F₁.cap (u, v)
    | (Sum.inr u, Sum.inr v) => F₂.cap (u, v)
    | _ => 0
  cap_nonneg a ha := by
    simp only [mem_union, mem_map, Function.Embedding.prodMap, Function.Embedding.coeFn_mk,
      Prod.exists] at ha
    rcases ha with ⟨u, v, h, rfl⟩ | ⟨u, v, h, rfl⟩
    · exact F₁.cap_nonneg _ h
    · exact F₂.cap_nonneg _ h
  ω := Sum.elim F₁.ω F₂.ω

omit [Fintype E] [DecidableEq E] in
/-- The form of one isolated node of weight `C` (the function `single C` of a capped linear
summand). -/
def node (C : ℝ) : CutForm Unit where
  D := ∅
  loopless a ha := absurd ha (notMem_empty a)
  cap _ := 0
  cap_nonneg _ _ := le_rfl
  ω _ := C

end CutForm

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
/-- The weights of a form on `Option E`: the weight of the node `none` if it lies in `T`, and the
weights of the old nodes of `T`. -/
lemma sum_option_weights (ω : Option E → ℝ) (T : Finset (Option E)) :
    ∑ o ∈ T, ω o = (if none ∈ T then ω none else 0) + ∑ e ∈ eraseNone T, ω (some e) :=
  sum_option_finset T ω

/-- **`lem:cutforms`(c)** (`stoc-sections/appD-hardness.tex:110-120`, proof lines 143-150): let `g`
be given by a cut form `(D, cap, ω)` on `E`. Then (i) `g` plus a modular function `S ↦ y(S)`
has the form with `ω` replaced by `ω + y`; (ii) the direct sum of `g` and a modular singleton `π_F`
on a new element `b` has the form
with `b` added as an isolated node of weight `F`; (iii) the one-element extension
`g'(S) = g(S)`, `g'(S ∪ {b}) = g(S) + K − d(S)` with `d ≥ 0` has the form with the node `b` of
weight `K − d(E)` and the arcs `b → e` of capacity `d_e`; and the direct sum of two functions given
by cut forms has the disjoint union of the two forms as a cut form. The new element `b` is `none`
in `Option E`, the direct sum with a modular singleton is `addSingleton`, the extension is `extend`
(its `h = f − d` is `subMod`).

The proof's steps, in the paper's order ((iii) first): (1) for (iii), on `S ⊆ E` the arcs of `D`
contribute `cut_D(S)` to the cuts of both `S` and `S ∪ {b}`; (2) the new arcs `b → e` contribute
nothing to the cut of `S`; (3) to the cut of `S ∪ {b}` they contribute `d(E) − d(S)`, and the weight
`K − d(E)` of `b` is counted there, which gives `g''(S) = g'(S)` and `g''(S ∪ {b}) = g'(S ∪ {b})`;
(4) the other operations add modular terms (i) or add two forms on disjoint sets: an isolated node
adds nothing to any cut and adds its weight to the sets that contain it (ii); (5) in a disjoint
union no arc joins `E_1` and `E_2`, so cut and weight split. -/
theorem cutforms_c {E₂ : Type*} [Fintype E₂] [DecidableEq E₂] {g : Finset E → ℝ}
    {F : CutForm E} (hF : ∀ S, g S = F.fn S) :
    (∀ (y : E → ℝ) S, g S + ∑ e ∈ S, y e = (F.addModular y).fn S) ∧
    (∀ (Fb : ℝ) T, addSingleton g Fb T = (F.addNode Fb).fn T) ∧
    (∀ {d : E → ℝ} (hd : ∀ e, 0 ≤ d e) (K : ℝ) T, extend g d K T = (F.extendForm hd K).fn T) ∧
    (∀ {g₂ : Finset E₂ → ℝ} {F₂ : CutForm E₂},
      (∀ S, g₂ S = F₂.fn S) → ∀ T, dsum g g₂ T = (F.dsumForm F₂).fn T) := by
  -- (1) "For the extension, let `g''` be the function of the extended form on `E ∪ {b}`, and let
  -- `S ⊆ E`. The arcs of `D` join nodes of `E`, so they contribute `cut_D(S)` to the cuts of both
  -- `S` and `S ∪ {b}`."
  have hiii : ∀ {d : E → ℝ} (hd : ∀ e, 0 ≤ d e) (K : ℝ) T,
      extend g d K T = (F.extendForm hd K).fn T := by
    intro d hd K T
    have h1 := F.sum_someArcs d T
    -- (2), (3) "The new arcs `b → e` leave `b`, so they contribute nothing to the cut of `S`. To
    -- the cut of `S ∪ {b}` they contribute `∑_{e ∈ E ∖ S} d_e = d(E) − d(S)`,"
    have h2 : ∑ a ∈ CutForm.newArcs (E := E) with a.1 ∈ T ∧ a.2 ∉ T, F.optCap d a =
        if none ∈ T then ∑ e, d e - ∑ e ∈ eraseNone T, d e else 0 := by
      rw [CutForm.newArcs, filter_map, sum_map]
      simp only [Function.comp_def, CutForm.arcFromNone_apply, CutForm.optCap]
      by_cases hn : none ∈ T
      · simp only [hn, true_and, ↓reduceIte]
        have : ∑ e, d e = ∑ e ∈ univ.filter (fun e => some e ∉ T), d e +
            ∑ e ∈ eraseNone T, d e := by
          rw [← sum_filter_add_sum_filter_not univ fun e => some e ∉ T]
          congr 1
          refine sum_congr ?_ fun _ _ => rfl
          ext e
          simp [mem_eraseNone]
        linarith
      · simp [hn]
    have hcut : (F.extendForm hd K).cut T =
        F.cut (eraseNone T) + if none ∈ T then ∑ e, d e - ∑ e ∈ eraseNone T, d e else 0 := by
      rw [show (F.extendForm hd K).cut T = ∑ a ∈ F.someArcs ∪ CutForm.newArcs with
          a.1 ∈ T ∧ a.2 ∉ T, F.optCap d a from rfl, filter_union,
        sum_union (disjoint_filter_filter (F.disjoint_someArcs_newArcs)), h1, h2]
    -- "and the weight `K − d(E)` of `b` is counted there as well. Hence `g''(S) = g(S) = g'(S)`
    -- and `g''(S ∪ {b}) = g(S) + d(E) − d(S) + K − d(E) = g'(S ∪ {b})`."
    simp only [CutForm.fn, hcut, sum_option_weights, extend, subMod, hF]
    simp only [CutForm.extendForm, Option.elim]
    by_cases hn : none ∈ T
    · simp only [hn, ↓reduceIte]
      ring
    · simp only [hn, ↓reduceIte]
      ring
  -- (4) "The other operations add modular terms or add two forms on disjoint sets." (i): replace
  -- `ω` by `ω + y`.
  have hi : ∀ (y : E → ℝ) S, g S + ∑ e ∈ S, y e = (F.addModular y).fn S := fun y S => by
    rw [hF, CutForm.fn_addModular]
  -- (ii) "An isolated node `b` of weight `F` adds nothing to any cut and adds `F` to the weight of
  -- exactly the sets that contain `b`, which gives `(g ⊕ π_F)(S) = g(S ∩ E) + π_F(S ∩ {b})`."
  have hii : ∀ (Fb : ℝ) T, addSingleton g Fb T = (F.addNode Fb).fn T := fun Fb T => by
    have hcut : (F.addNode Fb).cut T = F.cut (eraseNone T) := F.sum_someArcs 0 T
    simp only [CutForm.fn, hcut, sum_option_weights, addSingleton, hF]
    simp only [CutForm.addNode, Option.elim]
    ring
  -- (5) "For two cut forms on disjoint sets `E_1` and `E_2`, no arc joins `E_1` and `E_2`, so the
  -- cut and the weight of `S ⊆ E_1 ∪ E_2` in the disjoint union are those of `S ∩ E_1` plus those
  -- of `S ∩ E_2`."
  have hdu : ∀ {g₂ : Finset E₂ → ℝ} {F₂ : CutForm E₂},
      (∀ S, g₂ S = F₂.fn S) → ∀ T, dsum g g₂ T = (F.dsumForm F₂).fn T := by
    intro g₂ F₂ hF₂ T
    have hdisj : Disjoint (F.D.map (Function.Embedding.inl.prodMap Function.Embedding.inl))
        (F₂.D.map (Function.Embedding.inr.prodMap Function.Embedding.inr)) := by
      rw [disjoint_left]
      intro a ha ha'
      simp only [mem_map, Function.Embedding.prodMap, Function.Embedding.coeFn_mk,
        Prod.exists] at ha ha'
      obtain ⟨u, v, -, rfl⟩ := ha
      obtain ⟨u', v', -, h⟩ := ha'
      simp at h
    have hcut : (F.dsumForm F₂).cut T = F.cut T.toLeft + F₂.cut T.toRight := by
      unfold CutForm.cut CutForm.dsumForm
      dsimp only
      rw [filter_union, sum_union (disjoint_filter_filter hdisj), filter_map, filter_map,
        sum_map, sum_map]
      congr 1
      · refine sum_congr ?_ fun a _ => ?_
        · ext a
          simp [Function.comp_def, Prod.map]
        · rcases a with ⟨u, v⟩
          rfl
      · refine sum_congr ?_ fun a _ => ?_
        · ext a
          simp [Function.comp_def, Prod.map]
        · rcases a with ⟨u, v⟩
          rfl
    have hω : ∑ e ∈ T, (F.dsumForm F₂).ω e =
        ∑ e ∈ T.toLeft, F.ω e + ∑ e ∈ T.toRight, F₂.ω e := by
      conv_lhs => rw [← toLeft_disjSum_toRight (u := T)]
      rw [sum_disjSum]
      rfl
    simp only [CutForm.fn, hcut, hω, dsum, hF, hF₂]
    ring
  exact ⟨hi, hii, hiii, hdu⟩

/-- **`lem:cutforms`** (Lemma C.3, `stoc-sections/appD-hardness.tex:106-122`): (a) every
function given by a cut form as in (`eq:cutform`) is submodular. (b) The cut form `(D, cap, ω)`
defines a polymatroid rank function if and only if, for every `e ∈ E`, `ω_e` is at least the total
capacity of the arcs of `D` that enter `e`. In particular, membership in `𝒞_cut` is decided in
polynomial time. (c) Let `g` be given by a cut form `(D, cap, ω)` on `E`. Then each of the following
functions has a cut form: (i) `g` plus a modular function `S ↦ y(S)`: replace `ω` by `ω + y`; (ii)
the direct sum of `g` and a modular singleton `π_F` on a new element `b`: add `b` as an isolated
node of weight `F`; (iii) the one-element extension `g'(S) = g(S)`, `g'(S ∪ {b}) = g(S) + K − d(S)`
with `d ≥ 0`: add the node `b` with weight `K − d(E)` and the arcs `b → e` of capacity `d_e`. The
direct sum of two functions given by cut forms has the disjoint union of the two forms as a cut
form.

Cut forms are real here (the header of this file). The sentence "In particular, membership in
`𝒞_cut` is decided in polynomial time" of (b) is formalised only as the shape of the check, for
rational data: `RatInst.inCcut_iff` (`Stoc/Hardness/Encoding.lean`, later in the import chain),
`3|E|` comparisons of rationals; its running time is not. Its parts are `cutforms_a`, `cutforms_b`
and `cutforms_c`; their docstrings give the paper's steps. -/
theorem cutforms :
    -- (a)
    (∀ F : CutForm E, Submodular F.fn) ∧
    -- (b)
    (∀ F : CutForm E, IsRankFunction F.fn ↔ ∀ e, ∑ a ∈ F.D with a.2 = e, F.cap a ≤ F.ω e) ∧
    -- (c)
    ∀ {E₂ : Type*} [Fintype E₂] [DecidableEq E₂] {g : Finset E → ℝ} {F : CutForm E},
      (∀ S, g S = F.fn S) →
      (∀ (y : E → ℝ) S, g S + ∑ e ∈ S, y e = (F.addModular y).fn S) ∧
      (∀ (Fb : ℝ) T, addSingleton g Fb T = (F.addNode Fb).fn T) ∧
      (∀ {d : E → ℝ} (hd : ∀ e, 0 ≤ d e) (K : ℝ) T, extend g d K T = (F.extendForm hd K).fn T) ∧
      (∀ {g₂ : Finset E₂ → ℝ} {F₂ : CutForm E₂},
        (∀ S, g₂ S = F₂.fn S) → ∀ T, dsum g g₂ T = (F.dsumForm F₂).fn T) :=
  ⟨cutforms_a, cutforms_b, cutforms_c⟩

/-! ### Corollaries: the operations keep a cut form -/

theorem HasCutForm.add_modular {g : Finset E → ℝ} (h : HasCutForm g) (y : E → ℝ) :
    HasCutForm fun S => g S + ∑ e ∈ S, y e := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.addModular y, (cutforms_c (E₂ := Unit) hF).1 y⟩

theorem HasCutForm.addSingleton {g : Finset E → ℝ} (h : HasCutForm g) (Fb : ℝ) :
    HasCutForm (addSingleton g Fb) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.addNode Fb, (cutforms_c (E₂ := Unit) hF).2.1 Fb⟩

theorem HasCutForm.extend {g : Finset E → ℝ} (h : HasCutForm g) {d : E → ℝ}
    (hd : ∀ e, 0 ≤ d e) (K : ℝ) : HasCutForm (extend g d K) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.extendForm hd K, (cutforms_c (E₂ := Unit) hF).2.2.1 hd K⟩

theorem HasCutForm.dsum {E₂ : Type*} [Fintype E₂] [DecidableEq E₂] {g : Finset E → ℝ}
    {g₂ : Finset E₂ → ℝ} (h : HasCutForm g) (h₂ : HasCutForm g₂) : HasCutForm (dsum g g₂) := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨F₂, hF₂⟩ := h₂
  exact ⟨F.dsumForm F₂, (cutforms_c hF).2.2.2 hF₂⟩

/-- The function of one element with capacity `C` is given by one isolated node of weight `C`. -/
theorem hasCutForm_single (C : ℝ) : HasCutForm (single C) := by
  refine ⟨CutForm.node C, fun T => ?_⟩
  rcases finset_unit T with rfl | rfl
  · simp [single, CutForm.fn, CutForm.cut, CutForm.node]
  · simp [single, CutForm.fn, CutForm.cut, CutForm.node]

/-- Adding a capped linear summand (`knob`), a direct sum with a modular singleton, keeps a cut
form (`lem:cutforms`(c)(ii), in the form of the disjoint union with an isolated node). -/
theorem HasCutForm.knob {g : Finset E → ℝ} (h : HasCutForm g) (C : ℝ) :
    HasCutForm (knob g C) :=
  h.dsum (hasCutForm_single C)

end PartC

/-! ### `lem:translation`(a), with its sentence on cut forms -/

section TranslationA

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **`lem:translation`(a)** (Lemma B.11, `stoc-sections/appB-tools.tex:240-241`, proof
`appB-tools.tex:262-276`): for `g` submodular with `g(∅) = 0`, `m, β > 0`, `(μ_α, μ_θ)` with
`d_e = (μ_θ − μ_α m_e)/β_e ≥ 0` for all `e ∈ E`, `K ∈ ℝ` and a new element `b` (`none` in
`Option E`) with `m_b, β_b > 0`, the function `g'` (`extend g d K`) is submodular with
`g'(∅) = 0`; and if `g` is given by a cut form, then so is `g'` (`lem:cutforms`(c)(iii)). The STOC
version asks for rational `K` and `d` in the sentence on cut forms; cut forms are real here (the bit
model is in `Stoc/Hardness/Encoding.lean`, see the header of this file), so that hypothesis is
absent. This statement comes after `lem:cutforms` in the import chain, in this file;
`Stoc.Hardness.translation_a` (`Stoc/Hardness/Translation.lean`) is its first sentence.

Steps: (1)–(4) the marginal values of `g'` do not increase as the set grows, and
`g'(∅) = g(∅) = 0`, so `g'` is submodular with `g'(∅) = 0` (`translation_a`); (5) the statement on
cut forms is `lem:cutforms`(c)(iii): add the node `b` with weight `K − d(E)` and the arcs `b → e` of
capacity `d_e` for `e ∈ E` (`HasCutForm.extend`, with the form `CutForm.extendForm`). The
positivity hypotheses are not used. -/
theorem translation_a_cutForm {g : Finset E → ℝ} {m' β' : Option E → ℝ} (hg : Submodular g)
    (hg0 : g ∅ = 0) (hm : ∀ o, 0 < m' o) (hβ : ∀ o, 0 < β' o) (μα μθ : ℝ)
    (hd : ∀ e, 0 ≤ (μθ - μα * m' (some e)) / β' (some e)) (K : ℝ) :
    Submodular (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K) ∧
      extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K ∅ = 0 ∧
      (HasCutForm g →
        HasCutForm (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K)) := by
  -- (1)–(4) "We show that the marginal values of `g'` do not increase as the set grows. … As
  -- `g'(∅) = g(∅) = 0`, this proves that `g'` is submodular with `g'(∅) = 0`." (`translation_a`)
  obtain ⟨h1, h2⟩ := translation_a hg hg0 hm hβ μα μθ hd K
  -- (5) "The statement on cut forms is `lem:cutforms`(c)(iii): add the node `b` with weight
  -- `K − d(E)` and the arcs `b → e` of capacity `d_e` for `e ∈ E`."
  -- The Lean has real `K` and `d` (`HasCutForm.extend`, with the form `CutForm.extendForm`).
  exact ⟨h1, h2, fun h => h.extend hd K⟩

/-- **`lem:translation`** (Lemma B.11, `stoc-sections/appB-tools.tex:230-255`): let `g : 2^E → ℝ` be
submodular with `g(∅) = 0`, let `m, β ∈ ℝ^E_{>0}` and `t := m/β`. Let `(μ_α, μ_θ) ∈ ℝ²` be such
that `d_e := (μ_θ − μ_α m_e)/β_e ≥ 0` for all `e ∈ E`, let `K ∈ ℝ`, and let `b ∉ E` be a new element
with `m_b, β_b > 0` and `t_b := m_b/β_b`. Define `g'(S) := g(S)` and
`g'(S ∪ {b}) := g(S) + K − d(S)` for `S ⊆ E` (`extend g d K`). Then the following hold, where
`F^{g'}` is taken with respect to `t` and `β⁻¹` extended by `t_b` and `1/β_b`. (a) The function `g'`
is submodular with `g'(∅) = 0`. If `g` is given by a cut form and `K` and `d` are rational, then
`g'` is given by a cut form (`lem:cutforms`(c)(iii)). (b) For all `α, θ ∈ ℝ` and `T ⊆ E`,
`F^{g'}_{α,θ}(T) = F^g_{α,θ}(T)` and
`F^{g'}_{α,θ}(T ∪ {b}) = F^g_{α−μ_α,θ−μ_θ}(T) + K − α t_b + θ/β_b`. (c)
`F^{g−d}_{α,θ} = F^g_{α−μ_α,θ−μ_θ}` on `2^E` for all `α, θ ∈ ℝ`, and for every `α ∈ ℝ`,
`ξ^{g−d}(α) = ξ^g(α − μ_α) − d` and `ρ^{g−d}(α) = ρ^g(α − μ_α) + μ_θ`, with the full-plane best
responses and marginals of `g − d` (`shiftFun`) and `g` taken with respect to `m` and `β`. Moreover,
`A^{g−d}_θ(α) = A^g_{θ−μ_θ}(α − μ_α)` for all `α, θ ∈ ℝ`. Parts (b) and (c) do not use `d ≥ 0`. In
particular, (c) holds for every `(μ_α, μ_θ) ∈ ℝ²`.

The new element `b` is `none` in `Option E`; `m` and `β` extended by `m_b` and `β_b` are `m'` and
`β'`, so that `m = m' ∘ some` and `β = β' ∘ some`. The hypothesis `d ≥ 0` is in (a) alone, as the
lemma's last sentence says that (b) and (c) do not use it, and `K` is in (a) and (b), the parts in
which `g'` occurs; cut forms are real here, so (a) has no rationality hypothesis. Its parts are
`translation_a_cutForm`, `translation_b` and `translation_c`; their docstrings give the paper's
steps. -/
theorem translation {g : Finset E → ℝ} {m' β' : Option E → ℝ} (hg : Submodular g)
    (hg0 : g ∅ = 0) (hm : ∀ o, 0 < m' o) (hβ : ∀ o, 0 < β' o) (μα μθ : ℝ) :
    -- (a)
    ((∀ e, 0 ≤ (μθ - μα * m' (some e)) / β' (some e)) → ∀ K : ℝ,
      Submodular (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K) ∧
        extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K ∅ = 0 ∧
        (HasCutForm g →
          HasCutForm (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K))) ∧
    -- (b)
    (∀ (K α θ : ℝ) (T : Finset E),
      levelFun (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K) m' β' α θ
          (T.map Function.Embedding.some) =
        levelFun g (fun e => m' (some e)) (fun e => β' (some e)) α θ T ∧
      levelFun (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K) m' β' α θ
          (insertNone T) =
        levelFun g (fun e => m' (some e)) (fun e => β' (some e)) (α - μα) (θ - μθ) T + K -
          α * (m' none / β' none) + θ * (1 / β' none)) ∧
    -- (c) the shift
    ((∀ (α θ : ℝ) (S : Finset E),
        levelFun (shiftFun g (fun e => m' (some e)) (fun e => β' (some e)) μθ μα)
            (fun e => m' (some e)) (fun e => β' (some e)) α θ S =
          levelFun g (fun e => m' (some e)) (fun e => β' (some e)) (α - μα) (θ - μθ) S) ∧
      (∀ α : ℝ, xi (shiftFun g (fun e => m' (some e)) (fun e => β' (some e)) μθ μα)
          (fun e => m' (some e)) (fun e => β' (some e)) α =
        fun e => xi g (fun e => m' (some e)) (fun e => β' (some e)) (α - μα) e -
          (μθ - μα * m' (some e)) / β' (some e)) ∧
      (∀ α : ℝ, rho (shiftFun g (fun e => m' (some e)) (fun e => β' (some e)) μθ μα)
          (fun e => m' (some e)) (fun e => β' (some e)) α =
        fun e => rho g (fun e => m' (some e)) (fun e => β' (some e)) (α - μα) e + μθ) ∧
      ∀ α θ : ℝ, levelSet (fun e => m' (some e)) (fun e => β' (some e)) α
          (xi (shiftFun g (fun e => m' (some e)) (fun e => β' (some e)) μθ μα)
            (fun e => m' (some e)) (fun e => β' (some e)) α) θ =
        levelSet (fun e => m' (some e)) (fun e => β' (some e)) (α - μα)
          (xi g (fun e => m' (some e)) (fun e => β' (some e)) (α - μα)) (θ - μθ)) :=
  ⟨fun hd K => translation_a_cutForm hg hg0 hm hβ μα μθ hd K,
    fun K α θ T => translation_b hg hg0 hm hβ μα μθ K α θ T,
    translation_c hg hg0 (fun e => hm (some e)) (fun e => hβ (some e)) μα μθ⟩

end TranslationA

end

end Hardness

end Stoc
