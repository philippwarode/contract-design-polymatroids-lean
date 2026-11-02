-- stamp r8 2026-11-02
import Mathlib

/-!
# Polymatroids

The STOC version (`Contract_Design_for_Polymatroids/stoc.tex`), Section 2, Preliminaries
(`stoc-sections/02-preliminaries.tex`): submodular set functions (the lattice form of the STOC
version, and the form of diminishing returns, not in the paper), rank functions of polymatroids,
the independence polyhedron `P₊(f)` and tight sets; and Proposition `prop:tight` of Appendix B.1
(`sec:A-bestresponse`, `appB-quadratic.tex:32-34`: tight sets are closed under union and
intersection; `tight`).

Mathlib has matroids, but no polymatroids and no submodular set functions, so the notions are
set up here. Sets are `Finset`s of a type `E`, vectors are functions `E → ℝ`, and `x(S)` is
written `∑ e ∈ S, x e`.

The STOC version assumes a finite nonempty ground set ("Let `E` be a finite nonempty ground set",
`02-preliminaries.tex:4`). The Lean takes `E` with `Fintype E` and assumes `Nonempty E`, or
`n ≥ 1`, only where a proof uses it (`lem:A-tiebreak`, `lem:A-candidates`, `lem:A-lineartime`, and
the second and third parts of `thm:bitlength`); every other statement holds for `E = ∅` as well
and so implies the paper's, as for the reward bound `r̄ > 0` of the contract model of Section 2
(`ContractDesignPolymatroids/Approximation/Agent.lean`).

Taken over on 2026-10-20 from `Paper/Preliminaries/Polymatroid.lean` (the paper at Overleaf f035b19)
for the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

open Finset

variable {E : Type*} [DecidableEq E]

/-- Submodularity in the lattice form: `f(X ∪ Y) + f(X ∩ Y) ≤ f(X) + f(Y)`
(`stoc-sections/02-preliminaries.tex:4`). -/
def Submodular (f : Finset E → ℝ) : Prop :=
  ∀ X Y : Finset E, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y

/-- Submodularity in the form of diminishing returns (not in the paper: the STOC version defines
submodularity in the lattice form only, `stoc-sections/02-preliminaries.tex:4`; the proofs here use
this form as well): for `X ⊆ Y` and `e ∉ Y`, `f(X ∪ {e}) − f(X) ≥ f(Y ∪ {e}) − f(Y)`. -/
def DiminishingReturns (f : Finset E → ℝ) : Prop :=
  ∀ ⦃X Y : Finset E⦄ ⦃e : E⦄, X ⊆ Y → e ∉ Y → f (insert e Y) - f Y ≤ f (insert e X) - f X

/-- The lattice form gives diminishing returns (not in the paper: the STOC version has only the
lattice form, `stoc-sections/02-preliminaries.tex:4`). -/
theorem Submodular.diminishingReturns {f : Finset E → ℝ} (hf : Submodular f) :
    DiminishingReturns f := by
  intro X Y e hXY he
  have h := hf (insert e X) Y
  have h1 : insert e X ∪ Y = insert e Y := by
    rw [insert_union, union_eq_right.mpr hXY]
  have h2 : insert e X ∩ Y = X := by
    ext a
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨rfl | ha, hY⟩
      · exact absurd hY he
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, hXY ha⟩
  rw [h1, h2] at h
  linarith

/-- Diminishing returns give the lattice form (not in the paper: the STOC version has only the
lattice form, `stoc-sections/02-preliminaries.tex:4`). -/
theorem DiminishingReturns.submodular {f : Finset E → ℝ} (hf : DiminishingReturns f) :
    Submodular f := by
  -- For `A ⊆ B` and `D` disjoint from `B`: `f(B ∪ D) − f(B) ≤ f(A ∪ D) − f(A)`.
  have key : ∀ D A B : Finset E, A ⊆ B → Disjoint D B →
      f (B ∪ D) - f B ≤ f (A ∪ D) - f A := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro A B _ _; simp
    | insert d D hd ih =>
      intro A B hAB hdisj
      have hdB : d ∉ B := disjoint_left.mp hdisj (mem_insert_self d D)
      have hDB : Disjoint D B := disjoint_of_subset_left (subset_insert d D) hdisj
      have h1 := ih A B hAB hDB
      have hdBD : d ∉ B ∪ D := by
        rw [mem_union]
        rintro (h | h)
        · exact hdB h
        · exact hd h
      have h2 := hf (union_subset_union hAB (Subset.refl D)) hdBD
      rw [union_insert, union_insert]
      linarith
  intro X Y
  have h := key (Y \ X) (X ∩ Y) X inter_subset_left sdiff_disjoint
  have h1 : X ∪ Y \ X = X ∪ Y := union_sdiff_self_eq_union
  have h2 : X ∩ Y ∪ Y \ X = Y := by
    rw [union_comm, inter_comm]
    exact sdiff_union_inter Y X
  rw [h1, h2] at h
  linarith

/-- The two forms of submodularity agree (not in the paper: the STOC version has only the lattice
form, `stoc-sections/02-preliminaries.tex:4`). -/
theorem submodular_iff_diminishingReturns {f : Finset E → ℝ} :
    Submodular f ↔ DiminishingReturns f :=
  ⟨Submodular.diminishingReturns, DiminishingReturns.submodular⟩

/-- A (polymatroid) rank function: submodular, normalized and monotone
(`stoc-sections/02-preliminaries.tex:4`). -/
structure IsRankFunction (f : Finset E → ℝ) : Prop where
  empty : f ∅ = 0
  mono : Monotone f
  submod : Submodular f

theorem IsRankFunction.nonneg {f : Finset E → ℝ} (hf : IsRankFunction f) (S : Finset E) :
    0 ≤ f S :=
  hf.empty ▸ hf.mono (empty_subset S)

/-- The independence polyhedron `P₊(f) = {x ∈ ℝ^E_{≥0} : x(S) ≤ f(S) for all S ⊆ E}`
(`stoc-sections/02-preliminaries.tex:5-7`). -/
def indepPoly (f : Finset E → ℝ) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ S : Finset E, ∑ e ∈ S, x e ≤ f S}

theorem zero_mem_indepPoly {f : Finset E → ℝ} (hf : IsRankFunction f) :
    (0 : E → ℝ) ∈ indepPoly f :=
  ⟨fun _ => le_rfl, fun S => by simpa using hf.nonneg S⟩

omit [DecidableEq E] in
/-- The base polyhedron `B(f) := {x ∈ P₊(f) : x(E) = f(E)} = B_{(±)}(f) ∩ ℝ^E_{≥0}` of a
polymatroid rank function `f` (`stoc-sections/appB-tools.tex:27`), which the proof of
`lem:fullplane`(g) uses (`B_{(±)}(f) = B(f)`, `appB-tools.tex:219`). -/
def basePoly [Fintype E] (f : Finset E → ℝ) : Set (E → ℝ) :=
  {x | x ∈ indepPoly f ∧ ∑ e, x e = f univ}

omit [DecidableEq E] in
/-- `P₊(f)` is downward closed: `0 ≤ x ≤ y ∈ P₊(f)` implies `x ∈ P₊(f)`. -/
theorem mem_indepPoly_of_le {f : Finset E → ℝ} {x y : E → ℝ} (hy : y ∈ indepPoly f)
    (h0 : ∀ e, 0 ≤ x e) (hle : ∀ e, x e ≤ y e) : x ∈ indepPoly f :=
  ⟨h0, fun S => (sum_le_sum fun e _ => hle e).trans (hy.2 S)⟩

omit [DecidableEq E] in
/-- For `x ∈ P₊(f)`, a set `S` is tight if `x(S) = f(S)`
(`stoc-sections/02-preliminaries.tex:8`). -/
def IsTight (f : Finset E → ℝ) (x : E → ℝ) (S : Finset E) : Prop :=
  ∑ e ∈ S, x e = f S

/-- `prop:tight` for a submodular `f` (not in the paper: the STOC version cites Schrijver,
Theorem 44.2, without proof): if `S` and `S'` are tight with respect to `x ∈ P₊(f)`, then so are
`S ∪ S'` and `S ∩ S'`. The proof is the standard computation
`x(S ∪ S') + x(S ∩ S') = x(S) + x(S') = f(S) + f(S') ≥ f(S ∪ S') + f(S ∩ S')`
`≥ x(S ∪ S') + x(S ∩ S')`. -/
theorem tight_union_inter {f : Finset E → ℝ} (hf : Submodular f) {x : E → ℝ}
    (hx : x ∈ indepPoly f) {S S' : Finset E} (hS : IsTight f x S) (hS' : IsTight f x S') :
    IsTight f x (S ∪ S') ∧ IsTight f x (S ∩ S') := by
  unfold IsTight at *
  have h := sum_union_inter (s₁ := S) (s₂ := S') (f := x)
  have h1 := hx.2 (S ∪ S')
  have h2 := hx.2 (S ∩ S')
  have h3 := hf S S'
  constructor <;> linarith

/-- **`prop:tight`** (Proposition B.1, `stoc-sections/appB-quadratic.tex:32-34`; Schrijver, Theorem
44.2, which the STOC version cites without proof): for a polymatroid `(E, f)` and every `x ∈ P₊(f)`,
the tight sets are closed under union and intersection. Proof: `tight_union_inter`. -/
theorem tight {f : Finset E → ℝ} (hf : IsRankFunction f) {x : E → ℝ} (hx : x ∈ indepPoly f)
    {S S' : Finset E} (hS : IsTight f x S) (hS' : IsTight f x S') :
    IsTight f x (S ∪ S') ∧ IsTight f x (S ∩ S') :=
  tight_union_inter hf.submod hx hS hS'

omit [DecidableEq E] in
/-- The reward `r(x) = mᵀx` of the model (Section 2), shared by the linear model
(`ContractDesignPolymatroids/Linear/Linear.lean`) and the quadratic one (`ContractDesignPolymatroids/OptimalShare/Reward.lean`). -/
def reward [Fintype E] (m x : E → ℝ) : ℝ :=
  ∑ e, m e * x e

end Stoc
