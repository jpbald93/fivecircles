import Mathlib

open Complex ComplexConjugate EuclideanGeometry

namespace Fivecircles

/-- Twice the argument of `z`, as an angle; it is an angle modulo `π`. -/
noncomputable def th (z : ℂ) : Real.Angle := (2 : ℤ) • (arg z : Real.Angle)

/-- Imaginary part of the cross-ratio numerator `(a-c)(b-d)·conj((a-d)(b-c))`. It vanishes
exactly when `a, b, c, d` lie on a common circle or line. -/
def cd (a b c d : ℂ) : ℝ := ((a - c) * (b - d) * conj ((a - d) * (b - c))).im

/-- Imaginary part of `(x-z)·conj(y-z)`; it vanishes exactly when `x, y, z` are collinear. -/
def col3 (x y z : ℂ) : ℝ := ((x - z) * conj (y - z)).im

lemma th_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) : th (z * w) = th z + th w := by
  simp only [th, arg_mul_coe_angle hz hw, smul_add]

lemma th_conj (z : ℂ) : th (conj z) = -th z := by
  simp only [th, arg_conj_coe_angle, smul_neg]

lemma th_neg (z : ℂ) : th (-z) = th z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · simp only [th, arg_neg_coe_angle hz, smul_add, Real.Angle.two_zsmul_coe_pi, add_zero]

lemma th_sub_comm (p q : ℂ) : th (p - q) = th (q - p) := by
  rw [← neg_sub, th_neg]

lemma th_eq_zero_iff (z : ℂ) : th z = 0 ↔ z.im = 0 := by
  rw [th, Real.Angle.two_zsmul_eq_zero_iff, arg_coe_angle_eq_iff_eq_toReal,
    arg_coe_angle_eq_iff_eq_toReal, Real.Angle.toReal_zero, Real.Angle.toReal_pi,
    arg_eq_zero_iff, arg_eq_pi_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  · intro h
    rcases le_or_gt 0 z.re with h' | h'
    · exact Or.inl ⟨h', h⟩
    · exact Or.inr ⟨h', h⟩

lemma cd_eq_zero_iff {a b c d : ℂ} (h1 : a ≠ c) (h2 : b ≠ d) (h3 : a ≠ d) (h4 : b ≠ c) :
    cd a b c d = 0 ↔ th (a - c) + th (b - d) = th (a - d) + th (b - c) := by
  have e1 : a - c ≠ 0 := sub_ne_zero.2 h1
  have e2 : b - d ≠ 0 := sub_ne_zero.2 h2
  have e3 : a - d ≠ 0 := sub_ne_zero.2 h3
  have e4 : b - c ≠ 0 := sub_ne_zero.2 h4
  have e5 : conj ((a - d) * (b - c)) ≠ 0 := by rw [Ne, map_eq_zero]; exact mul_ne_zero e3 e4
  rw [cd, ← th_eq_zero_iff, th_mul (mul_ne_zero e1 e2) e5, th_mul e1 e2, th_conj, th_mul e3 e4,
    ← sub_eq_add_neg, sub_eq_zero]

lemma col3_eq_zero_iff {x y z : ℂ} (h1 : x ≠ z) (h2 : y ≠ z) :
    col3 x y z = 0 ↔ th (x - z) = th (y - z) := by
  have e1 : x - z ≠ 0 := sub_ne_zero.2 h1
  have e2 : conj (y - z) ≠ 0 := by rw [Ne, map_eq_zero]; exact sub_ne_zero.2 h2
  rw [col3, ← th_eq_zero_iff, th_mul e1 e2, th_conj, ← sub_eq_add_neg, sub_eq_zero]

lemma cd_s12 {a b c d : ℂ} (h : cd a b c d = 0) : cd b a c d = 0 := by
  simp only [cd, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im] at h ⊢
  linear_combination -h

lemma cd_s23 {a b c d : ℂ} (h : cd a b c d = 0) : cd a c b d = 0 := by
  simp only [cd, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im] at h ⊢
  linear_combination -h

lemma cd_s34 {a b c d : ℂ} (h : cd a b c d = 0) : cd a b d c = 0 := by
  simp only [cd, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im] at h ⊢
  linear_combination -h

lemma col3_s12 {x y z : ℂ} (h : col3 x y z = 0) : col3 y x z = 0 := by
  simp only [col3, mul_im, sub_re, sub_im, conj_re, conj_im] at h ⊢
  linear_combination -h

lemma col3_s23 {x y z : ℂ} (h : col3 x y z = 0) : col3 x z y = 0 := by
  simp only [col3, mul_im, sub_re, sub_im, conj_re, conj_im] at h ⊢
  linear_combination -h

/-- Bridge: three points of a collinear set satisfy `col3 = 0`. -/
lemma col3_of_collinear {s : Set ℂ} (h : Collinear ℝ s) {x y z : ℂ} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ s) : col3 x y z = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem hz).1 h
  obtain ⟨r, rfl⟩ := hv x hx
  obtain ⟨u, rfl⟩ := hv y hy
  simp only [col3, vadd_eq_add, add_sub_cancel_right, real_smul, mul_im, mul_re, conj_re,
    conj_im, ofReal_re, ofReal_im]
  ring

/-- Bridge: four points of a concyclic set satisfy `cd = 0`. -/
lemma cd_of_concyclic {s : Set ℂ} (h : Concyclic s) {a b c d : ℂ} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hd : d ∈ s) : cd a b c d = 0 := by
  obtain ⟨O, r, hr⟩ := h.1
  have key : ∀ p ∈ s, (p.re - O.re) ^ 2 + (p.im - O.im) ^ 2 = r ^ 2 := by
    intro p hp
    rw [← hr p hp, Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im]
    ring
  have h1 := key a ha
  have h2 := key b hb
  have h3 := key c hc
  have h4 := key d hd
  simp only [cd, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im]
  linear_combination
    (b.re * c.im - b.re * d.im - b.im * c.re + b.im * d.re + c.re * d.im - c.im * d.re) * h1 +
    (-a.re * c.im + a.re * d.im + a.im * c.re - a.im * d.re - c.re * d.im + c.im * d.re) * h2 +
    (a.re * b.im - a.re * d.im - a.im * b.re + a.im * d.re + b.re * d.im - b.im * d.re) * h3 +
    (-a.re * b.im + a.re * c.im + a.im * b.re - a.im * c.re - b.re * c.im + b.im * c.re) * h4

/-- Bridge: if `p, q, r` are not collinear and every point `x` of `s` has `cd p q r x = 0`,
then `s` is concyclic (the centre is the circumcentre of `p, q, r`). -/
lemma concyclic_of {s : Set ℂ} {p q r : ℂ} (hD : col3 r q p ≠ 0)
    (hs : ∀ x ∈ s, cd p q r x = 0) : Concyclic s := by
  set D := 2 * ((q.re - p.re) * (r.im - p.im) - (q.im - p.im) * (r.re - p.re)) with hDdef
  have hD' : D ≠ 0 := by
    simp only [col3, mul_im, sub_re, sub_im, conj_re, conj_im] at hD
    intro h0; apply hD; rw [hDdef] at h0; linear_combination (1 / 2 : ℝ) * h0
  obtain ⟨Ox, hOx⟩ : ∃ Ox : ℝ, D * Ox = p.re * D + ((r.im - p.im) * ((q.re - p.re) ^ 2 +
      (q.im - p.im) ^ 2) - (q.im - p.im) * ((r.re - p.re) ^ 2 + (r.im - p.im) ^ 2)) :=
    ⟨_, mul_div_cancel₀ _ hD'⟩
  obtain ⟨Oy, hOy⟩ : ∃ Oy : ℝ, D * Oy = p.im * D + ((q.re - p.re) * ((r.re - p.re) ^ 2 +
      (r.im - p.im) ^ 2) - (r.re - p.re) * ((q.re - p.re) ^ 2 + (q.im - p.im) ^ 2)) :=
    ⟨_, mul_div_cancel₀ _ hD'⟩
  refine ⟨⟨⟨Ox, Oy⟩, dist p ⟨Ox, Oy⟩, fun x hx => ?_⟩,
    coplanar_of_finrank_eq_two s Complex.finrank_real_complex⟩
  have h := hs x hx
  simp only [cd, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im] at h
  have key : D * (((x.re - Ox) ^ 2 + (x.im - Oy) ^ 2) - ((p.re - Ox) ^ 2 + (p.im - Oy) ^ 2)) = 0 := by
    linear_combination (-2 : ℝ) * h - 2 * (x.re - p.re) * hOx - 2 * (x.im - p.im) * hOy
  have key' := (mul_eq_zero.1 key).resolve_left hD'
  rw [Complex.dist_eq, Complex.dist_eq,
    ← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, Complex.sq_norm,
    Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, sub_im]
  linear_combination key'

/-- Bridge: if every point `x` of `s` has `col3 x q p = 0` (with `p ≠ q`, `p ∈ s`),
then `s` is collinear. -/
lemma collinear_of {s : Set ℂ} {p q : ℂ} (hp : p ∈ s) (hpq : p ≠ q)
    (hs : ∀ x ∈ s, col3 x q p = 0) : Collinear ℝ s := by
  have hn : (q.re - p.re) ^ 2 + (q.im - p.im) ^ 2 ≠ 0 := by
    intro h0
    apply hpq
    have h1 : q.re - p.re = 0 := by nlinarith [sq_nonneg (q.re - p.re), sq_nonneg (q.im - p.im)]
    have h2 : q.im - p.im = 0 := by nlinarith [sq_nonneg (q.re - p.re), sq_nonneg (q.im - p.im)]
    apply Complex.ext <;> linarith
  rw [collinear_iff_of_mem hp]
  refine ⟨q - p, fun x hx => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ((q.re - p.re) ^ 2 + (q.im - p.im) ^ 2) * t =
      (x.re - p.re) * (q.re - p.re) + (x.im - p.im) * (q.im - p.im) :=
    ⟨_, mul_div_cancel₀ _ hn⟩
  refine ⟨t, ?_⟩
  have h := hs x hx
  simp only [col3, mul_im, sub_re, sub_im, conj_re, conj_im] at h
  have e1 : ((q.re - p.re) ^ 2 + (q.im - p.im) ^ 2) * (x.re - (t * (q.re - p.re) + p.re)) = 0 := by
    linear_combination -(q.re - p.re) * ht - (q.im - p.im) * h
  have e2 : ((q.re - p.re) ^ 2 + (q.im - p.im) ^ 2) * (x.im - (t * (q.im - p.im) + p.im)) = 0 := by
    linear_combination -(q.im - p.im) * ht + (q.re - p.re) * h
  have f1 := (mul_eq_zero.1 e1).resolve_left hn
  have f2 := (mul_eq_zero.1 e2).resolve_left hn
  apply Complex.ext <;>
    simp only [vadd_eq_add, real_smul, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
      sub_re, sub_im] <;> linarith


/-- The core of the pentagram computation: with lines `ℓ_i ⊇ {A(i-1), A i, T(i+1), T(i-1)}`
and circles `{A(i-1), A i, T i, M(i-1), M i}`, the four points `M 0, …, M 3` satisfy the
concyclicity condition `cd = 0`. -/
theorem core (A T M : Fin 5 → ℂ) (hA : Function.Injective A) (hT : Function.Injective T)
    (hM : Function.Injective M) (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j)
    (hTM : ∀ i j, T i ≠ M j)
    (hL : ∀ i, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hC : ∀ i, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ)) :
    cd (M 0) (M 1) (M 2) (M 3) = 0 := by
  have hL0 : Collinear ℝ ({A 4, A 0, T 1, T 4} : Set ℂ) := hL 0
  have hL1 : Collinear ℝ ({A 0, A 1, T 2, T 0} : Set ℂ) := hL 1
  have hL2 : Collinear ℝ ({A 1, A 2, T 3, T 1} : Set ℂ) := hL 2
  have hL3 : Collinear ℝ ({A 2, A 3, T 4, T 2} : Set ℂ) := hL 3
  have hL4 : Collinear ℝ ({A 3, A 4, T 0, T 3} : Set ℂ) := hL 4
  have hC0 : Concyclic ({A 4, A 0, T 0, M 4, M 0} : Set ℂ) := hC 0
  have hC1 : Concyclic ({A 0, A 1, T 1, M 0, M 1} : Set ℂ) := hC 1
  have hC2 : Concyclic ({A 1, A 2, T 2, M 1, M 2} : Set ℂ) := hC 2
  have hC3 : Concyclic ({A 2, A 3, T 3, M 2, M 3} : Set ℂ) := hC 3
  have hC4 : Concyclic ({A 3, A 4, T 4, M 3, M 4} : Set ℂ) := hC 4
  have k1 := col3_of_collinear hL0 (x := A 0) (y := T 4) (z := T 1) (by simp) (by simp) (by simp)
  have g2 := (col3_eq_zero_iff (hAT 0 1) (hT.ne (by decide : (4 : Fin 5) ≠ 1))).1 k1
  rw [th_sub_comm (T 4) (T 1)] at g2
  have k3 := col3_of_collinear hL0 (x := A 0) (y := T 1) (z := A 4) (by simp) (by simp) (by simp)
  have g4 := (col3_eq_zero_iff (hA.ne (by decide : (0 : Fin 5) ≠ 4)) (hAT 4 1).symm).1 k3
  rw [th_sub_comm (T 1) (A 4)] at g4
  have k5 := col3_of_collinear hL0 (x := A 0) (y := A 4) (z := T 1) (by simp) (by simp) (by simp)
  have g6 := (col3_eq_zero_iff (hAT 0 1) (hAT 4 1)).1 k5
  have k7 := col3_of_collinear hL0 (x := A 0) (y := T 4) (z := A 4) (by simp) (by simp) (by simp)
  have g8 := (col3_eq_zero_iff (hA.ne (by decide : (0 : Fin 5) ≠ 4)) (hAT 4 4).symm).1 k7
  rw [th_sub_comm (T 4) (A 4)] at g8
  have k9 := col3_of_collinear hL2 (x := T 1) (y := A 1) (z := A 2) (by simp) (by simp) (by simp)
  have g10 := (col3_eq_zero_iff (hAT 2 1).symm (hA.ne (by decide : (1 : Fin 5) ≠ 2))).1 k9
  rw [th_sub_comm (T 1) (A 2)] at g10
  have k11 := col3_of_collinear hL2 (x := T 1) (y := A 2) (z := A 1) (by simp) (by simp) (by simp)
  have g12 := (col3_eq_zero_iff (hAT 1 1).symm (hA.ne (by decide : (2 : Fin 5) ≠ 1))).1 k11
  rw [th_sub_comm (T 1) (A 1), th_sub_comm (A 2) (A 1)] at g12
  have k13 := col3_of_collinear hL2 (x := T 1) (y := A 1) (z := T 3) (by simp) (by simp) (by simp)
  have g14 := (col3_eq_zero_iff (hT.ne (by decide : (1 : Fin 5) ≠ 3)) (hAT 1 3)).1 k13
  have k15 := col3_of_collinear hL2 (x := T 1) (y := T 3) (z := A 1) (by simp) (by simp) (by simp)
  have g16 := (col3_eq_zero_iff (hAT 1 1).symm (hAT 1 3).symm).1 k15
  rw [th_sub_comm (T 1) (A 1), th_sub_comm (T 3) (A 1)] at g16
  have k17 := col3_of_collinear hL2 (x := T 1) (y := A 2) (z := T 3) (by simp) (by simp) (by simp)
  have g18 := (col3_eq_zero_iff (hT.ne (by decide : (1 : Fin 5) ≠ 3)) (hAT 2 3)).1 k17
  have k19 := col3_of_collinear hL4 (x := A 4) (y := T 3) (z := A 3) (by simp) (by simp) (by simp)
  have g20 := (col3_eq_zero_iff (hA.ne (by decide : (4 : Fin 5) ≠ 3)) (hAT 3 3).symm).1 k19
  rw [th_sub_comm (A 4) (A 3), th_sub_comm (T 3) (A 3)] at g20
  have k21 := cd_of_concyclic hC3 (a := A 2) (b := A 3) (c := T 3) (d := M 3) (by simp) (by simp) (by simp) (by simp)
  have g22 := (cd_eq_zero_iff (hAT 2 3) (hAM 3 3) (hAM 2 3) (hAT 3 3)).1 k21
  have k23 := cd_of_concyclic hC4 (a := A 3) (b := T 4) (c := A 4) (d := M 3) (by simp) (by simp) (by simp) (by simp)
  have g24 := (cd_eq_zero_iff (hA.ne (by decide : (3 : Fin 5) ≠ 4)) (hTM 4 3) (hAM 3 3) (hAT 4 4).symm).1 k23
  rw [th_sub_comm (T 4) (A 4)] at g24
  have z25 : th (T 1 - T 4) + th (A 2 - M 3) = th (A 2 - T 1) + th (T 4 - M 3) := by
    linear_combination (norm := abel) -g2 - g4 + g6 + g8 - g10 + g12 + g14 - g16 - g18 + g20 - g22 - g24
  have c26 : cd (T 1) (M 3) (T 4) (A 2) = 0 := (cd_eq_zero_iff (hT.ne (by decide : (1 : Fin 5) ≠ 4)) (hAM 2 3).symm (hAT 2 1).symm (hTM 4 3).symm).2 (by
    rw [th_sub_comm (M 3) (A 2), th_sub_comm (T 1) (A 2), th_sub_comm (M 3) (T 4)]; exact z25)
  have k27 := col3_of_collinear hL1 (x := A 0) (y := T 2) (z := A 1) (by simp) (by simp) (by simp)
  have g28 := (col3_eq_zero_iff (hA.ne (by decide : (0 : Fin 5) ≠ 1)) (hAT 1 2).symm).1 k27
  rw [th_sub_comm (T 2) (A 1)] at g28
  have k29 := col3_of_collinear hL3 (x := T 4) (y := T 2) (z := A 2) (by simp) (by simp) (by simp)
  have g30 := (col3_eq_zero_iff (hAT 2 4).symm (hAT 2 2).symm).1 k29
  rw [th_sub_comm (T 4) (A 2), th_sub_comm (T 2) (A 2)] at g30
  have k31 := cd_of_concyclic hC1 (a := A 0) (b := A 1) (c := T 1) (d := M 1) (by simp) (by simp) (by simp) (by simp)
  have g32 := (cd_eq_zero_iff (hAT 0 1) (hAM 1 1) (hAM 0 1) (hAT 1 1)).1 k31
  have k33 := cd_of_concyclic hC1 (a := A 0) (b := T 1) (c := A 1) (d := M 1) (by simp) (by simp) (by simp) (by simp)
  have g34 := (cd_eq_zero_iff (hA.ne (by decide : (0 : Fin 5) ≠ 1)) (hTM 1 1) (hAM 0 1) (hAT 1 1).symm).1 k33
  rw [th_sub_comm (T 1) (A 1)] at g34
  have k35 := cd_of_concyclic hC2 (a := A 1) (b := A 2) (c := T 2) (d := M 1) (by simp) (by simp) (by simp) (by simp)
  have g36 := (cd_eq_zero_iff (hAT 1 2) (hAM 2 1) (hAM 1 1) (hAT 2 2)).1 k35
  have z37 : th (T 1 - T 4) + th (A 2 - M 1) = th (T 1 - M 1) + th (A 2 - T 4) := by
    linear_combination (norm := abel) -g2 + g28 - g30 + g32 - g34 + g36
  have c38 : cd (T 1) (A 2) (T 4) (M 1) = 0 := (cd_eq_zero_iff (hT.ne (by decide : (1 : Fin 5) ≠ 4)) (hAM 2 1) (hTM 1 1) (hAT 2 4)).2 (by
    exact z37)
  have k39 := col3_of_collinear hL3 (x := T 4) (y := A 2) (z := A 3) (by simp) (by simp) (by simp)
  have g40 := (col3_eq_zero_iff (hAT 3 4).symm (hA.ne (by decide : (2 : Fin 5) ≠ 3))).1 k39
  rw [th_sub_comm (T 4) (A 3)] at g40
  have k41 := cd_of_concyclic hC3 (a := A 2) (b := T 3) (c := A 3) (d := M 3) (by simp) (by simp) (by simp) (by simp)
  have g42 := (cd_eq_zero_iff (hA.ne (by decide : (2 : Fin 5) ≠ 3)) (hTM 3 3) (hAM 2 3) (hAT 3 3).symm).1 k41
  rw [th_sub_comm (T 3) (A 3)] at g42
  have k43 := cd_of_concyclic hC4 (a := A 3) (b := A 4) (c := T 4) (d := M 3) (by simp) (by simp) (by simp) (by simp)
  have g44 := (cd_eq_zero_iff (hAT 3 4) (hAM 4 3) (hAM 3 3) (hAT 4 4)).1 k43
  have z45 : th (A 4 - T 1) + th (T 3 - M 3) = th (T 1 - T 3) + th (A 4 - M 3) := by
    linear_combination (norm := abel) -g4 + g8 - g18 + g40 - g22 + g42 - g44
  have c46 : cd (T 1) (M 3) (A 4) (T 3) = 0 := (cd_eq_zero_iff (hAT 4 1).symm (hTM 3 3).symm (hT.ne (by decide : (1 : Fin 5) ≠ 3)) (hAM 4 3).symm).2 (by
    rw [th_sub_comm (T 1) (A 4), th_sub_comm (M 3) (T 3), th_sub_comm (M 3) (A 4)]; exact z45)
  have k47 := col3_of_collinear hL1 (x := A 0) (y := A 1) (z := T 0) (by simp) (by simp) (by simp)
  have g48 := (col3_eq_zero_iff (hAT 0 0) (hAT 1 0)).1 k47
  have k49 := col3_of_collinear hL1 (x := A 0) (y := T 0) (z := A 1) (by simp) (by simp) (by simp)
  have g50 := (col3_eq_zero_iff (hA.ne (by decide : (0 : Fin 5) ≠ 1)) (hAT 1 0).symm).1 k49
  rw [th_sub_comm (T 0) (A 1)] at g50
  have k51 := col3_of_collinear hL4 (x := A 4) (y := T 0) (z := T 3) (by simp) (by simp) (by simp)
  have g52 := (col3_eq_zero_iff (hAT 4 3) (hT.ne (by decide : (0 : Fin 5) ≠ 3))).1 k51
  have k53 := col3_of_collinear hL4 (x := A 4) (y := T 3) (z := T 0) (by simp) (by simp) (by simp)
  have g54 := (col3_eq_zero_iff (hAT 4 0) (hT.ne (by decide : (3 : Fin 5) ≠ 0))).1 k53
  rw [th_sub_comm (T 3) (T 0)] at g54
  have k55 := cd_of_concyclic hC0 (a := A 4) (b := A 0) (c := T 0) (d := M 0) (by simp) (by simp) (by simp) (by simp)
  have g56 := (cd_eq_zero_iff (hAT 4 0) (hAM 0 0) (hAM 4 0) (hAT 0 0)).1 k55
  have k57 := cd_of_concyclic hC1 (a := A 0) (b := T 1) (c := A 1) (d := M 0) (by simp) (by simp) (by simp) (by simp)
  have g58 := (cd_eq_zero_iff (hA.ne (by decide : (0 : Fin 5) ≠ 1)) (hTM 1 0) (hAM 0 0) (hAT 1 1).symm).1 k57
  rw [th_sub_comm (T 1) (A 1)] at g58
  have z59 : th (T 1 - T 3) + th (A 4 - M 0) = th (T 1 - M 0) + th (A 4 - T 3) := by
    linear_combination (norm := abel) -g48 + g50 + g14 - g16 - g52 + g54 - g56 - g58
  have c60 : cd (T 1) (A 4) (T 3) (M 0) = 0 := (cd_eq_zero_iff (hT.ne (by decide : (1 : Fin 5) ≠ 3)) (hAM 4 0) (hTM 1 0) (hAT 4 3)).2 (by
    exact z59)
  have k61 := col3_of_collinear hL3 (x := T 4) (y := A 2) (z := T 2) (by simp) (by simp) (by simp)
  have g62 := (col3_eq_zero_iff (hT.ne (by decide : (4 : Fin 5) ≠ 2)) (hAT 2 2)).1 k61
  rw [th_sub_comm (T 4) (T 2)] at g62
  have k63 := col3_of_collinear hL3 (x := T 4) (y := T 2) (z := A 3) (by simp) (by simp) (by simp)
  have g64 := (col3_eq_zero_iff (hAT 3 4).symm (hAT 3 2).symm).1 k63
  rw [th_sub_comm (T 4) (A 3), th_sub_comm (T 2) (A 3)] at g64
  have k65 := col3_of_collinear hL3 (x := T 4) (y := A 3) (z := T 2) (by simp) (by simp) (by simp)
  have g66 := (col3_eq_zero_iff (hT.ne (by decide : (4 : Fin 5) ≠ 2)) (hAT 3 2)).1 k65
  rw [th_sub_comm (T 4) (T 2)] at g66
  have k67 := col3_of_collinear hL4 (x := A 4) (y := T 0) (z := A 3) (by simp) (by simp) (by simp)
  have g68 := (col3_eq_zero_iff (hA.ne (by decide : (4 : Fin 5) ≠ 3)) (hAT 3 0).symm).1 k67
  rw [th_sub_comm (A 4) (A 3), th_sub_comm (T 0) (A 3)] at g68
  have k69 := col3_of_collinear hL4 (x := A 4) (y := A 3) (z := T 0) (by simp) (by simp) (by simp)
  have g70 := (col3_eq_zero_iff (hAT 4 0) (hAT 3 0)).1 k69
  have k71 := cd_of_concyclic hC2 (a := A 1) (b := A 2) (c := T 2) (d := M 2) (by simp) (by simp) (by simp) (by simp)
  have g72 := (cd_eq_zero_iff (hAT 1 2) (hAM 2 2) (hAM 1 2) (hAT 2 2)).1 k71
  have k73 := cd_of_concyclic hC3 (a := A 2) (b := T 3) (c := A 3) (d := M 2) (by simp) (by simp) (by simp) (by simp)
  have g74 := (cd_eq_zero_iff (hA.ne (by decide : (2 : Fin 5) ≠ 3)) (hTM 3 2) (hAM 2 2) (hAT 3 3).symm).1 k73
  rw [th_sub_comm (T 3) (A 3)] at g74
  have z75 : th (A 1 - T 0) + th (T 3 - M 2) = th (A 1 - M 2) + th (T 0 - T 3) := by
    linear_combination (norm := abel) g28 - g50 - g62 - g64 + g66 + g40 + g54 + g68 - g70 - g20 + g72 + g74
  have c76 : cd (A 1) (T 3) (T 0) (M 2) = 0 := (cd_eq_zero_iff (hAT 1 0) (hTM 3 2) (hAM 1 2) (hT.ne (by decide : (3 : Fin 5) ≠ 0))).2 (by
    rw [th_sub_comm (T 3) (T 0)]; exact z75)
  have k77 := cd_of_concyclic hC0 (a := A 4) (b := T 0) (c := A 0) (d := M 0) (by simp) (by simp) (by simp) (by simp)
  have g78 := (cd_eq_zero_iff (hA.ne (by decide : (4 : Fin 5) ≠ 0)) (hTM 0 0) (hAM 4 0) (hAT 0 0).symm).1 k77
  rw [th_sub_comm (A 4) (A 0), th_sub_comm (T 0) (A 0)] at g78
  have k79 := cd_of_concyclic hC1 (a := A 0) (b := A 1) (c := T 1) (d := M 0) (by simp) (by simp) (by simp) (by simp)
  have g80 := (cd_eq_zero_iff (hAT 0 1) (hAM 1 0) (hAM 0 0) (hAT 1 1)).1 k79
  have z81 : th (A 1 - T 3) + th (T 0 - M 0) = th (A 1 - M 0) + th (T 0 - T 3) := by
    linear_combination (norm := abel) -g4 + g6 - g16 + g54 - g56 + g78 - g80
  have c82 : cd (A 1) (T 0) (T 3) (M 0) = 0 := (cd_eq_zero_iff (hAT 1 3) (hTM 0 0) (hAM 1 0) (hT.ne (by decide : (0 : Fin 5) ≠ 3))).2 (by
    exact z81)
  have c83 : cd (T 1) (A 4) (M 0) (T 3) = 0 := (cd_s34 c60)
  have g84 := (cd_eq_zero_iff (hTM 1 0) (hAT 4 3) (hT.ne (by decide : (1 : Fin 5) ≠ 3)) (hAM 4 0)).1 c83
  have c85 : cd (T 1) (A 4) (M 3) (T 3) = 0 := (cd_s23 c46)
  have g86 := (cd_eq_zero_iff (hTM 1 3) (hAT 4 3) (hT.ne (by decide : (1 : Fin 5) ≠ 3)) (hAM 4 3)).1 c85
  have z87 : th (T 1 - M 0) + th (A 4 - M 3) = th (T 1 - M 3) + th (A 4 - M 0) := by
    linear_combination (norm := abel) g84 - g86
  have c88 : cd (T 1) (A 4) (M 0) (M 3) = 0 := (cd_eq_zero_iff (hTM 1 0) (hAM 4 3) (hTM 1 3) (hAM 4 0)).2 (by
    exact z87)
  have c89 : cd (T 1) (T 4) (M 1) (A 2) = 0 := (cd_s34 (cd_s23 c38))
  have g90 := (cd_eq_zero_iff (hTM 1 1) (hAT 2 4).symm (hAT 2 1).symm (hTM 4 1)).1 c89
  rw [th_sub_comm (T 4) (A 2), th_sub_comm (T 1) (A 2)] at g90
  have c91 : cd (T 1) (T 4) (M 3) (A 2) = 0 := (cd_s23 c26)
  have g92 := (cd_eq_zero_iff (hTM 1 3) (hAT 2 4).symm (hAT 2 1).symm (hTM 4 3)).1 c91
  rw [th_sub_comm (T 4) (A 2), th_sub_comm (T 1) (A 2)] at g92
  have z93 : th (T 1 - M 1) + th (T 4 - M 3) = th (T 1 - M 3) + th (T 4 - M 1) := by
    linear_combination (norm := abel) g90 - g92
  have c94 : cd (T 1) (T 4) (M 1) (M 3) = 0 := (cd_eq_zero_iff (hTM 1 1) (hTM 4 3) (hTM 1 3) (hTM 4 1)).2 (by
    exact z93)
  have c95 : cd (A 1) (T 0) (M 0) (T 3) = 0 := (cd_s34 c82)
  have g96 := (cd_eq_zero_iff (hAM 1 0) (hT.ne (by decide : (0 : Fin 5) ≠ 3)) (hAT 1 3) (hTM 0 0)).1 c95
  have c97 : cd (A 1) (T 0) (M 2) (T 3) = 0 := (cd_s34 (cd_s23 c76))
  have g98 := (cd_eq_zero_iff (hAM 1 2) (hT.ne (by decide : (0 : Fin 5) ≠ 3)) (hAT 1 3) (hTM 0 2)).1 c97
  have z99 : th (A 1 - M 0) + th (T 0 - M 2) = th (A 1 - M 2) + th (T 0 - M 0) := by
    linear_combination (norm := abel) g96 - g98
  have c100 : cd (A 1) (T 0) (M 0) (M 2) = 0 := (cd_eq_zero_iff (hAM 1 0) (hTM 0 2) (hAM 1 2) (hTM 0 0)).2 (by
    exact z99)
  have k101 := cd_of_concyclic hC2 (a := A 1) (b := M 1) (c := A 2) (d := M 2) (by simp) (by simp) (by simp) (by simp)
  have g102 := (cd_eq_zero_iff (hA.ne (by decide : (1 : Fin 5) ≠ 2)) (hM.ne (by decide : (1 : Fin 5) ≠ 2)) (hAM 1 2) (hAM 2 1).symm).1 k101
  rw [th_sub_comm (M 1) (A 2)] at g102
  have c103 : cd (T 1) (M 3) (T 4) (M 1) = 0 := (cd_s23 (cd_s34 c94))
  have g104 := (cd_eq_zero_iff (hT.ne (by decide : (1 : Fin 5) ≠ 4)) (hM.ne (by decide : (3 : Fin 5) ≠ 1)) (hTM 1 1) (hTM 4 3).symm).1 c103
  rw [th_sub_comm (M 3) (M 1), th_sub_comm (M 3) (T 4)] at g104
  have c105 : cd (T 1) (M 3) (A 4) (M 0) = 0 := (cd_s23 (cd_s34 c88))
  have g106 := (cd_eq_zero_iff (hAT 4 1).symm (hM.ne (by decide : (3 : Fin 5) ≠ 0)) (hTM 1 0) (hAM 4 3).symm).1 c105
  rw [th_sub_comm (T 1) (A 4), th_sub_comm (M 3) (M 0), th_sub_comm (M 3) (A 4)] at g106
  have c107 : cd (A 1) (T 0) (T 3) (M 2) = 0 := (cd_s23 c76)
  have g108 := (cd_eq_zero_iff (hAT 1 3) (hTM 0 2) (hAM 1 2) (hT.ne (by decide : (0 : Fin 5) ≠ 3))).1 c107
  have c109 : cd (A 1) (M 2) (T 0) (M 0) = 0 := (cd_s23 (cd_s34 c100))
  have g110 := (cd_eq_zero_iff (hAT 1 0) (hM.ne (by decide : (2 : Fin 5) ≠ 0)) (hAM 1 0) (hTM 0 2).symm).1 c109
  rw [th_sub_comm (M 2) (M 0), th_sub_comm (M 2) (T 0)] at g110
  have z111 : th (M 0 - M 2) + th (M 1 - M 3) = th (M 0 - M 3) + th (M 1 - M 2) := by
    linear_combination (norm := abel) g2 - g6 - g28 + g50 - g12 + g16 + g62 + g64 - g66 - g54 - g68 + g70 + g80 - g58 - g32 + g34 - g36 - g102 - g44 + g24 + g104 - g106 + g108 + g110
  have c112 : cd (M 0) (M 1) (M 2) (M 3) = 0 := (cd_eq_zero_iff (hM.ne (by decide : (0 : Fin 5) ≠ 2)) (hM.ne (by decide : (1 : Fin 5) ≠ 3)) (hM.ne (by decide : (0 : Fin 5) ≠ 3)) (hM.ne (by decide : (1 : Fin 5) ≠ 2))).2 (by
    exact z111)
  exact c112

lemma cd_cyc {a b c d : ℂ} (h : cd a b c d = 0) : cd b c d a = 0 := by
  simp only [cd, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im] at h ⊢
  linear_combination -h

/-- If `a, b, c` are collinear and distinct and `cd a b c x = 0`, then `x` lies on line `ab`. -/
lemma col3_of_cd {a b c x : ℂ} (hca : c ≠ a) (hcb : c ≠ b) (hc : col3 c b a = 0)
    (h : cd a b c x = 0) : col3 x b a = 0 := by
  have hK : (a.re - c.re) * (b.re - c.re) + (a.im - c.im) * (b.im - c.im) ≠ 0 := by
    intro hK
    have hc' := hc
    simp only [col3, mul_im, sub_re, sub_im, conj_re, conj_im] at hc'
    have e : ((a.re - c.re) ^ 2 + (a.im - c.im) ^ 2) * ((b.re - c.re) ^ 2 + (b.im - c.im) ^ 2) = 0 := by
      linear_combination
        ((a.re - c.re) * (b.re - c.re) + (a.im - c.im) * (b.im - c.im)) * hK +
        ((c.re - a.re) * -(b.im - a.im) + (c.im - a.im) * (b.re - a.re)) * hc'
    rcases mul_eq_zero.1 e with e | e
    · apply hca
      have h1 : a.re - c.re = 0 := by nlinarith [sq_nonneg (a.re - c.re), sq_nonneg (a.im - c.im)]
      have h2 : a.im - c.im = 0 := by nlinarith [sq_nonneg (a.re - c.re), sq_nonneg (a.im - c.im)]
      apply Complex.ext <;> linarith
    · apply hcb
      have h1 : b.re - c.re = 0 := by nlinarith [sq_nonneg (b.re - c.re), sq_nonneg (b.im - c.im)]
      have h2 : b.im - c.im = 0 := by nlinarith [sq_nonneg (b.re - c.re), sq_nonneg (b.im - c.im)]
      apply Complex.ext <;> linarith
  have e : ((a.re - c.re) * (b.re - c.re) + (a.im - c.im) * (b.im - c.im)) * col3 x b a = 0 := by
    simp only [cd, col3, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im] at h hc ⊢
    linear_combination h +
      ((x.re - a.re) * (x.re - b.re) + (x.im - a.im) * (x.im - b.im)) * hc
  exact (mul_eq_zero.1 e).resolve_left hK

/-- **Miquel's five circles theorem (pentagram form).**
Five lines `ℓ_0, …, ℓ_4` form a pentagram: `A i = ℓ_i ∩ ℓ_(i+1)` are the inner (pentagon)
vertices and `T i = ℓ_(i-1) ∩ ℓ_(i+1)` are the star tips, so line `ℓ_i` contains
`A (i-1), A i, T (i+1), T (i-1)` (hypothesis `hL`). Circle `i` is the circumcircle of the `i`-th
tip triangle `T i, A (i-1), A i`. Consecutive circles `i` and `i+1` meet at `A i`, and `M i` is
their second intersection point (hypothesis `hC`: circle `i` passes through `M (i-1)` and `M i`).
Then the five points `M i` lie on one circle (or, degenerately, one line). The distinctness
hypotheses exclude degenerate pentagrams. -/
theorem fivecircles (A T M : Fin 5 → ℂ) (hA : Function.Injective A) (hT : Function.Injective T)
    (hM : Function.Injective M) (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j)
    (hTM : ∀ i j, T i ≠ M j)
    (hL : ∀ i, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hC : ∀ i, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ)) :
    Concyclic (Set.range M) ∨ Collinear ℝ (Set.range M) := by
  -- the core computation, applied to the five cyclic relabellings
  have sh : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0 := by
    intro k
    have := core (fun i => A (i + k)) (fun i => T (i + k)) (fun i => M (i + k))
      (fun i j h => add_right_cancel (hA h)) (fun i j h => add_right_cancel (hT h))
      (fun i j h => add_right_cancel (hM h)) (fun i j => hAT _ _) (fun i j => hAM _ _)
      (fun i j => hTM _ _)
      (fun i => by
        have := hL (i + k)
        simp only [sub_add_eq_add_sub, add_right_comm i 1 k] at this ⊢
        exact this)
      (fun i => by
        have := hC (i + k)
        simp only [sub_add_eq_add_sub] at this ⊢
        exact this)
    simpa [add_comm] using this
  have h3 : cd (M 0) (M 1) (M 2) (M 3) = 0 := by simpa using sh 0
  have h4 : cd (M 0) (M 1) (M 2) (M 4) = 0 := by
    have := sh 4
    have e : cd (M 4) (M 0) (M 1) (M 2) = 0 := by simpa using this
    exact cd_cyc e
  have hall : ∀ x ∈ Set.range M, cd (M 0) (M 1) (M 2) x = 0 := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simp [cd]
    · simp [cd]
    · simp only [cd, Fin.reduceFinMk]
      rw [mul_conj, ofReal_im]
    · exact h3
    · exact h4
  by_cases hD : col3 (M 2) (M 1) (M 0) = 0
  · right
    refine collinear_of ⟨0, rfl⟩ (hM.ne (by decide : (0 : Fin 5) ≠ 1)) fun x hx => ?_
    exact col3_of_cd (hM.ne (by decide : (2 : Fin 5) ≠ 0)) (hM.ne (by decide : (2 : Fin 5) ≠ 1))
      hD (hall x hx)
  · left
    exact concyclic_of hD hall

end Fivecircles
