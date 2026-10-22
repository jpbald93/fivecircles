import Fivecircles.Basic

/-!
# Layer 14: Mathlib-only restatement and a witness for Miquel's five circles theorem

`l14_fivecircles` mentions only Mathlib notions (`Function.Injective`, `Collinear`, `Concyclic`,
`Set.range`); it is the library theorem itself, whose statement was already namespace-free.
`l14w_fivecircles` is an explicit pentagram in `ℂ` given by the five lines
`-2x = -1`, `2x - y = 0`, `2x - 2y = -4`, `x + y = 0`, `3x + y = 2`:
`A = (1/2, 1), (2, 4), (-1, 1), (1, -1), (1/2, 1/2)`,
`T = (2/5, 4/5), (1/2, 5/2), (0, 0), (0, 2), (1/2, -1/2)`,
`M = (4/5, 2/5), (7/5, -1/5), (2, 0), (2, 1), (1, 1)`.
All fifteen points are pairwise distinct. The five Miquel points lie on the circle with centre
`(3/2, 1/2)` and squared radius `1/2`, and they are **not** collinear, so the conclusion holds
through its `Concyclic` branch, with five distinct points.
-/

namespace Fivecircles

open Complex EuclideanGeometry

attribute [local instance] Complex.finrank_real_complex_fact

/-- Miquel's five circles theorem, Mathlib-only statement. -/
theorem l14_fivecircles (A T M : Fin 5 → ℂ) (hA : Function.Injective A)
    (hT : Function.Injective T) (hM : Function.Injective M) (hAT : ∀ i j, A i ≠ T j)
    (hAM : ∀ i j, A i ≠ M j) (hTM : ∀ i j, T i ≠ M j)
    (hL : ∀ i, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hC : ∀ i, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ)) :
    Concyclic (Set.range M) ∨ Collinear ℝ (Set.range M) :=
  fivecircles A T M hA hT hM hAT hAM hTM hL hC

/-! ### Bridges for explicit configurations -/

theorem l14b_collinear4 {a b c d : ℂ} (ta tb : ℝ) (ha : a = c + (ta : ℂ) * (d - c))
    (hb : b = c + (tb : ℂ) * (d - c)) : Collinear ℝ ({a, b, c, d} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := c) (by simp)]
  refine ⟨d - c, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨ta, by rw [ha, vadd_eq_add, Complex.real_smul]; ring⟩
  · exact ⟨tb, by rw [hb, vadd_eq_add, Complex.real_smul]; ring⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

theorem l14b_concyclic_of_normSq {s : Set ℂ} (O : ℂ) (r : ℝ) (h : ∀ x ∈ s, normSq (x - O) = r) :
    Concyclic s :=
  ⟨⟨O, Real.sqrt r, fun x hx => by rw [Complex.dist_eq, Complex.norm_def, h x hx]⟩,
    coplanar_of_fact_finrank_eq_two s⟩

theorem l14b_not_collinear {a b c : ℂ}
    (h : (b - a).re * (c - a).im - (b - a).im * (c - a).re ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  apply h
  rw [hs, ht]
  simp only [vadd_eq_add, add_sub_cancel_right, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ### Witness -/

/-- The pentagram vertices. -/
theorem l14w_fivecircles :
    let A : Fin 5 → ℂ := ![⟨1/2, 1⟩, ⟨2, 4⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨1/2, 1/2⟩]
    let T : Fin 5 → ℂ := ![⟨2/5, 4/5⟩, ⟨1/2, 5/2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1/2, -1/2⟩]
    let M : Fin 5 → ℂ := ![⟨4/5, 2/5⟩, ⟨7/5, -1/5⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩]
    (Function.Injective A ∧ Function.Injective T ∧ Function.Injective M ∧
      (∀ i j, A i ≠ T j) ∧ (∀ i j, A i ≠ M j) ∧ (∀ i j, T i ≠ M j) ∧
      (∀ i, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ)) ∧
      (∀ i, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ))) ∧
    Concyclic (Set.range M) ∧ ¬ Collinear ℝ (Set.range M) ∧
    (∀ x ∈ Set.range M, dist x ⟨3/2, 1/2⟩ = Real.sqrt (1/2)) := by
  intro A T M
  have inj : ∀ f : Fin 5 → ℂ, (∀ i j : Fin 5, i ≠ j → f i ≠ f j) → Function.Injective f :=
    fun f h i j hij => by by_contra hne; exact h i j hne hij
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine inj A fun i j hij => ?_
    fin_cases i <;> fin_cases j <;> simp [A, Complex.ext_iff] at hij ⊢ <;> norm_num
  · refine inj T fun i j hij => ?_
    fin_cases i <;> fin_cases j <;> simp [T, Complex.ext_iff] at hij ⊢ <;> norm_num
  · refine inj M fun i j hij => ?_
    fin_cases i <;> fin_cases j <;> simp [M, Complex.ext_iff] at hij ⊢ <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> simp [A, T, Complex.ext_iff] <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> simp [A, M, Complex.ext_iff] <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> simp [T, M, Complex.ext_iff] <;> norm_num
  · intro i; fin_cases i
    · exact l14b_collinear4 (2/3) (1/2) (by simp [A, T, Complex.ext_iff]; norm_num)
        (by simp [A, T, Complex.ext_iff]; norm_num)
    · exact l14b_collinear4 (5/4) 5 (by simp [A, T, Complex.ext_iff]; norm_num)
        (by simp [A, T, Complex.ext_iff]; norm_num)
    · exact l14b_collinear4 4 (-2) (by simp [A, T, Complex.ext_iff]; norm_num)
        (by simp [A, T, Complex.ext_iff]; norm_num)
    · exact l14b_collinear4 3 (-1) (by simp [A, T, Complex.ext_iff]; norm_num)
        (by simp [A, T, Complex.ext_iff]; norm_num)
    · exact l14b_collinear4 (-3/2) (-1/4) (by simp [A, T, Complex.ext_iff]; norm_num)
        (by simp [A, T, Complex.ext_iff]; norm_num)
  · intro i; fin_cases i
    · refine l14b_concyclic_of_normSq ⟨3/4, 3/4⟩ (1/8) fun x hx => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [A, T, M, Complex.normSq_apply] <;> norm_num
    · refine l14b_concyclic_of_normSq ⟨11/4, 7/4⟩ (45/8) fun x hx => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [A, T, M, Complex.normSq_apply] <;> norm_num
    · refine l14b_concyclic_of_normSq ⟨1, 2⟩ 5 fun x hx => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [A, T, M, Complex.normSq_apply] <;> norm_num
    · refine l14b_concyclic_of_normSq ⟨1/2, 1/2⟩ (5/2) fun x hx => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [A, T, M, Complex.normSq_apply] <;> norm_num
    · refine l14b_concyclic_of_normSq ⟨3/2, 0⟩ (5/4) fun x hx => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [A, T, M, Complex.normSq_apply] <;> norm_num
  · refine l14b_concyclic_of_normSq ⟨3/2, 1/2⟩ (1/2) fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;> simp [M, Complex.normSq_apply] <;> norm_num
  · intro hc
    refine l14b_not_collinear (a := M 0) (b := M 1) (c := M 2) (by simp [M]; norm_num)
      (hc.subset ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · rintro x ⟨i, rfl⟩
    rw [Complex.dist_eq, Complex.norm_def]
    congr 1
    fin_cases i <;> simp [M, Complex.normSq_apply] <;> norm_num

end Fivecircles
