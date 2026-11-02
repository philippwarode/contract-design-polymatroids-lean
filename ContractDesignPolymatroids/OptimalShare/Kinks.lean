-- stamp r5 2026-11-02
import Mathlib

/-!
# Kinks of real functions

Points near which a function `ℝ → ℝ` is not affine, and facts about them that the STOC version
uses without proof. The counting lemmas `finite_ncard_le_of_forall_finset` and
`card_le_two_of_no_triple` serve `ContractDesignPolymatroids/Subclasses/LinearPieces.lean`, and `affineAt_sup'` serves
step (2) of the proof of `thm:laminar` (`Stoc.affineAt_PiUp`, `ContractDesignPolymatroids/Subclasses/LaminarHeight.lean`).
`exists_affine_of_affineAt` is used for the pieces of `thm:pieces` (`Stoc.Tracing.affine_on_piece`)
and in `ContractDesignPolymatroids/OptimalShare/Exponential.lean`.

Taken over on 2026-10-20 from `Paper/OptimalShare/Kinks.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

open Set Filter Topology

/-- `g` is affine on a neighborhood of `α`. -/
def AffineAt (g : ℝ → ℝ) (α : ℝ) : Prop :=
  ∃ ε > 0, ∃ a b : ℝ, ∀ α' ∈ Ioo (α - ε) (α + ε), g α' = a + b * α'

/-- The kinks of `g`: the points near which `g` is not affine. -/
def kinks (g : ℝ → ℝ) : Set ℝ := {α | ¬ AffineAt g α}

/-! ### Affine pieces -/

/-- A function that agrees with `a + b x` on an open interval has derivative `b` there. -/
theorem hasDerivAt_of_eqOn_Ioo {g : ℝ → ℝ} {l r a b x : ℝ}
    (h : ∀ y ∈ Ioo l r, g y = a + b * y) (hx : x ∈ Ioo l r) : HasDerivAt g b x := by
  have hev : g =ᶠ[𝓝 x] fun y => a + b * y :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx.1 hx.2) h
  have hd : HasDerivAt (fun y => a + b * y) b x := by
    have := (hasDerivAt_id' x |>.const_mul b).const_add a
    rwa [mul_one] at this
  exact hd.congr_of_eventuallyEq hev

/-- A function that is continuous on `[a, b]` and affine near every point of `(a, b)` is affine on
`[a, b]`. -/
theorem exists_affine_of_affineAt {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (h : ∀ α ∈ Ioo a b, AffineAt g α) :
    ∃ c d : ℝ, ∀ α ∈ Icc a b, g α = c + d * α := by
  -- near every point of `(a, b)`, `g` has a derivative and `deriv g` is constant
  have hloc : ∀ α ∈ Ioo a b, ∃ s, HasDerivAt g s α ∧ deriv g =ᶠ[𝓝 α] fun _ => s := by
    intro α hα
    obtain ⟨ε, hε, a', b', h'⟩ := h α hα
    have hmem : α ∈ Ioo (α - ε) (α + ε) := ⟨by linarith, by linarith⟩
    refine ⟨b', hasDerivAt_of_eqOn_Ioo h' hmem, ?_⟩
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
    exact (hasDerivAt_of_eqOn_Ioo h' hx).deriv
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  -- so `deriv g` is constant on `(a, b)`
  have hd : ∀ x ∈ Ioo a b, deriv g x = deriv g ((a + b) / 2) := by
    have h2 : ∀ y ∈ Ioo a b, HasDerivAt (deriv g) 0 y := fun y hy => by
      obtain ⟨s, -, hs⟩ := hloc y hy
      exact (hasDerivAt_const y s).congr_of_eventuallyEq hs
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun y hy => (h2 y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (h2 y hy).deriv) hx hm
  set d := deriv g ((a + b) / 2)
  -- and `g x - d x` is constant on `(a, b)`
  have h3 : ∀ y ∈ Ioo a b, HasDerivAt (fun x => g x - d * x) 0 y := by
    intro y hy
    obtain ⟨s, hs, -⟩ := hloc y hy
    have hsd : s = d := hs.deriv.symm.trans (hd y hy)
    have := hs.sub (hasDerivAt_id' y |>.const_mul d)
    rw [hsd, mul_one, sub_self] at this
    exact this
  have h4 : ∀ x ∈ Ioo a b, g x - d * x = g ((a + b) / 2) - d * ((a + b) / 2) := fun x hx =>
    isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun x => g x - d * x) isPreconnected_Ioo
      (fun y hy => (h3 y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (h3 y hy).deriv) hx hm
  refine ⟨g ((a + b) / 2) - d * ((a + b) / 2), d, ?_⟩
  -- extend from `(a, b)` to `[a, b]` by continuity
  have heq : EqOn g (fun x => g ((a + b) / 2) - d * ((a + b) / 2) + d * x) (Ioo a b) := by
    intro x hx
    have := h4 x hx
    dsimp only
    linarith
  have hcont : Continuous fun x => g ((a + b) / 2) - d * ((a + b) / 2) + d * x := by
    fun_prop
  exact heq.of_subset_closure hg hcont.continuousOn Ioo_subset_Icc_self (closure_Ioo hab.ne).ge

/-! ### Counting -/

/-- A set of reals whose finite subsets have at most `n` elements is finite with at most `n`
elements. -/
theorem finite_ncard_le_of_forall_finset {S : Set ℝ} {n : ℕ}
    (h : ∀ V : Finset ℝ, (V : Set ℝ) ⊆ S → V.card ≤ n) : S.Finite ∧ S.ncard ≤ n := by
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨V, hV, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
    have := h V hV
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact h hfin.toFinset hfin.coe_toFinset.le

/-- A finite set of reals without three points `x < y < z` has at most two elements. -/
theorem card_le_two_of_no_triple {W : Finset ℝ}
    (h : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, x < y → y < z → False) : W.card ≤ 2 := by
  by_contra hc
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 (not_le.1 hc)
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact h x hx y hy z hz h1 h3
  · exact h x hx z hz y hy h2 h3
  · linarith
  · exact h z hz x hx y hy h2 h1
  · exact h y hy x hx z hz h1 h2
  · linarith
  · exact h y hy z hz x hx h3 h2
  · exact h z hz y hy x hx h3 h1

/-! ### Maxima of finitely many functions -/

/-- The maximum of finitely many continuous functions is affine near `α₀` if each of them is and
`α₀` is not a boundary point of a set on which two of them agree. -/
theorem affineAt_sup' {ι : Type*} {F : Finset ι} (hF : F.Nonempty) {φ : ι → ℝ → ℝ}
    (hc : ∀ i ∈ F, Continuous (φ i)) {α₀ : ℝ} (ha : ∀ i ∈ F, AffineAt (φ i) α₀)
    (hfr : ∀ i ∈ F, ∀ j ∈ F, α₀ ∉ frontier {α | φ i α = φ j α}) :
    AffineAt (fun α => F.sup' hF fun i => φ i α) α₀ := by
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hF fun i => φ i α₀
  -- near `α₀`, every `φ j` lies below `φ i₀`
  have hle : ∀ᶠ α in 𝓝 α₀, ∀ j ∈ F, φ j α ≤ φ i₀ α := by
    refine (Filter.eventually_all_finset F).2 fun j hj => ?_
    by_cases heq : φ j α₀ = φ i₀ α₀
    · -- `α₀` lies in `{φ j = φ i₀}` but not on its boundary, so in its interior
      have hint : α₀ ∈ interior {α | φ j α = φ i₀ α} := by
        by_contra hni
        exact hfr j hj i₀ hi₀ ⟨subset_closure heq, hni⟩
      filter_upwards [mem_interior_iff_mem_nhds.1 hint] with α hα
      exact le_of_eq hα
    · -- `φ j α₀ < φ i₀ α₀`, which persists near `α₀`
      have hlt : φ j α₀ < φ i₀ α₀ := by
        refine lt_of_le_of_ne ?_ heq
        rw [← hmax]
        exact Finset.le_sup' (fun i => φ i α₀) hj
      filter_upwards [(hc j hj).continuousAt.eventually_lt (hc i₀ hi₀).continuousAt hlt]
        with α hα
      exact hα.le
  obtain ⟨ε₁, hε₁, a, b, hab⟩ := ha i₀ hi₀
  obtain ⟨ε₂, hε₂, hε₂'⟩ := Metric.eventually_nhds_iff.1 hle
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, a, b, fun α hα => ?_⟩
  have hm1 := min_le_left ε₁ ε₂
  have hm2 := min_le_right ε₁ ε₂
  have hd : dist α α₀ < ε₂ := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hα.1, hα.2]
  have h1 : α ∈ Ioo (α₀ - ε₁) (α₀ + ε₁) := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  rw [← hab α h1]
  exact le_antisymm (Finset.sup'_le hF _ (hε₂' hd)) (Finset.le_sup' (fun i => φ i α) hi₀)

end Stoc
