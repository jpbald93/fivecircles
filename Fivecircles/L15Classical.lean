import Fivecircles.Basic

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.
-/


/-!
# Paper D — classical statements D1–D7 (blind formalisation)

All statements live in the Euclidean plane `Pt := EuclideanSpace ℝ (Fin 2)`.
Constructed objects (second intersection points, Clifford points, Fermat points,
Thébault circles, auxiliary circumcentres, bisector feet) are passed in as data
together with their DEFINING property; well-definedness facts that are needed only
to make such data exist are stated separately as `_obligation` theorems.
-/

open EuclideanGeometry

noncomputable section

namespace Fivecircles.Classical

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ## D1 — Clifford's circle theorems -/

/-- OWN DEFINITION. General position hypothesis of D1 for `n` circles `c i` through a
common point `M`: genuine circles (positive radius), pairwise distinct, `P i j` is a
second common point of `c i` and `c j` different from `M`, and for any three circles the
three second points are not collinear. (Since distinct circles meet in at most two points,
`P i j` is uniquely determined by these conditions.) -/
structure CliffordGP (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt) (P : Fin n → Fin n → Pt) :
    Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  second_mem : ∀ i j, i ≠ j → P i j ∈ c i ∧ P i j ∈ c j
  second_ne : ∀ i j, i ≠ j → P i j ≠ M
  noncollinear : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {P i j, P i k, P j k}

/-- OWN DEFINITION. `X` lies on every circle `Γ_ijk` (through the non-collinear points
`P i j, P i k, P j k`) for `i, j, k` pairwise distinct in `S`. For `S` with four elements
this says that `X` is a common point of the four circles of D1(a) (a "Clifford point").
Because `P i j, P i k, P j k` are non-collinear, `Cospherical {P i j, P i k, P j k, X}`
means exactly that `X` lies on their (unique) circumcircle. -/
def OnAllGamma {n : ℕ} (P : Fin n → Fin n → Pt) (S : Finset (Fin n)) (X : Pt) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k →
    Cospherical ({P i j, P i k, P j k, X} : Set Pt)

/-- D1(a), Clifford n = 4: the four circles `Γ_123, Γ_124, Γ_134, Γ_234` have a common
point. -/
def classical_D1_a (c : Fin 4 → Sphere Pt) (M : Pt) (P : Fin 4 → Fin 4 → Pt)
    (h : CliffordGP 4 c M P) : Prop := 
    ∃ X : Pt, OnAllGamma P Finset.univ X


/-- D1(b), Clifford n = 5: the five Clifford points `X l` (of the four circles obtained by
omitting circle `l`) lie on one circle. -/
def classical_D1_b (c : Fin 5 → Sphere Pt) (M : Pt) (P : Fin 5 → Fin 5 → Pt)
    (h : CliffordGP 5 c M P) (X : Fin 5 → Pt)
    (hX : ∀ l, OnAllGamma P (Finset.univ.erase l) (X l))
    -- EXTRA HYPOTHESIS: "general position" — the Clifford point of each four circles is
    -- well defined (the four Γ-circles have exactly one common point); otherwise "the
    -- point given by part (a)" is not determined.
    (hXu : ∀ l Y, OnAllGamma P (Finset.univ.erase l) Y → Y = X l)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical (range X) ∨ Collinear ℝ (range X)`
    -- ("circle or line", the inversive form).
    (hnc : ¬ Collinear ℝ (Set.range X)) : Prop := 
    Cospherical (Set.range X)


/-- D1(c), Clifford n = 6: for each `m`, the five Clifford points `X m l` (`l ≠ m`) of the
five circles other than `m` lie on a circle `C m` (part (b)); these six circles have a
common point. `X m l` is the Clifford point of the four circles other than `m, l`. -/
def classical_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) : Prop := 
    ∃ Y : Pt, ∀ m, Y ∈ C m


/-- OWN DEFINITION. Data of Clifford's chain for `n` circles `c i` through `M`, levels
indexed by subsets `S` of the circles: `circ S` (for `|S|` odd) is the circle and `pt S`
(for `|S|` even) the point attached to `S`.
* level 1: `circ {i} = c i`;
* level 2: `pt {i,j}` is the second intersection of `c i, c j` (≠ `M`);
* odd level `|S| = 2k+1 ≥ 3`: `circ S` passes through the `|S|` points `pt (S \ {i})`,
  which are not collinear (general position), so `circ S` is uniquely determined;
* even level `|S| = 2k ≥ 4`: `pt S` lies on the `|S|` circles `circ (S \ {i})` and is their
  unique common point (general position).
All levels strictly below `n` are part of the data/hypotheses (they are the lower
instances of the chain); the theorems below assert the top level `n`. -/
structure CliffordChain (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt) : Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  level_one : ∀ i, circ {i} = c i
  level_two : ∀ S : Finset (Fin n), S.card = 2 →
    pt S ≠ M ∧ ∀ i ∈ S, pt S ∈ circ (S.erase i)
  odd_mem : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt (S.erase i) ∈ circ S
  odd_gp : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ¬ Collinear ℝ ((fun i => pt (S.erase i)) '' (S : Set (Fin n)))
  even_mem : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt S ∈ circ (S.erase i)
  even_gp : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ Y : Pt, (∀ i ∈ S, Y ∈ circ (S.erase i)) → Y = pt S

/-- D1(d), Clifford's chain, even step (all even `n ≥ 4`): the `n` circles of level
`n - 1` pass through one common point.
(The case `n = 2` is the general-position hypothesis `level_two` itself.) -/
def classical_D1_d_even (n : ℕ) (hn : 4 ≤ n) (he : Even n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ) : Prop := 
    ∃ Y : Pt, ∀ i, Y ∈ circ (Finset.univ.erase i)


/-- D1(d), Clifford's chain, odd step (all odd `n ≥ 3`): the `n` points of level `n - 1`
lie on one circle. -/
def classical_D1_d_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ)
    -- EXTRA HYPOTHESIS: the top-level points are not collinear ("one circle"). For `n = 3`
    -- this is exactly the non-collinearity hypothesis of (a).
    -- AMBIGUOUS: drop it and conclude `Cospherical … ∨ Collinear ℝ …` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range fun i => pt (Finset.univ.erase i))) : Prop := 
    Cospherical (Set.range fun i => pt (Finset.univ.erase i))


/-! ## D2 — Miquel's pentagram (five circles) theorem -/

/-- D2. Five lines `ℓ 0, …, ℓ 4` in general position (no two parallel, no three
concurrent), labelled in the cyclic order of the sides of the inner pentagon: its vertices
are `V i = ℓ i ∩ ℓ (i+1)`, the star points are `T i = ℓ (i-1) ∩ ℓ (i+1)`, and the outer
triangle `i` (bounded by `ℓ (i-1), ℓ i, ℓ (i+1)`) has vertices `V (i-1), V i, T i` and
circumcircle `ω i`.
AMBIGUOUS: the labelling is only required to be cyclic as above; we do not additionally
require the inner pentagon to be convex / the figure to be a "star" (alternative: add a
hypothesis that the `V i` form a convex pentagon with the `T i` outside it).
Consecutive circles `ω i, ω (i+1)` meet in the inner vertex `V i` and in
a second point `Q i`. Then the five points `Q i` lie on one circle. -/
def classical_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    -- The classical statement presupposes a second point; AMBIGUOUS: if `ω i, ω (i+1)` are
    -- tangent at `V i` one could take `Q i = V i` (here such configurations are excluded by
    -- the requirement `Q i ≠ V i`).
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical ∨ Collinear` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range Q)) : Prop := 
    Cospherical (Set.range Q)


/-- D2 obligation (well-formedness only): for five lines in general position the
intersection points `V i`, `T i` exist and the three vertices of each outer triangle are
non-collinear, so the circumcircles `ω i` exist (and are unique). -/
def classical_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) : Prop := 
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt)


/-! ## D3 — Lester's theorem -/

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected OUTWARDLY on side
`q r` of triangle `p q r` (opposite side of line `q r` from `p`). -/
def IsOuterApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SOppSide p X

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected INWARDLY on side
`q r` of triangle `p q r` (same side of line `q r` as `p`). -/
def IsInnerApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SSameSide p X

/-- OWN DEFINITION. First Fermat point (first isogonic centre): common point of the lines
joining each vertex to the apex of the outward equilateral triangle on the opposite side. -/
def IsFirstFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsOuterApex a b c A' ∧ IsOuterApex b c a B' ∧ IsOuterApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- OWN DEFINITION. Second Fermat point (second isogonic centre): same with the inward
equilateral triangles. -/
def IsSecondFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsInnerApex a b c A' ∧ IsInnerApex b c a B' ∧ IsInnerApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- D3, Lester's theorem: in a scalene triangle the two Fermat points, the circumcentre and
the nine-point centre are concyclic. -/
def classical_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt)


/-- D3 obligation (well-formedness only): both Fermat points exist (the second one needs
the triangle not to be equilateral; scalene suffices). -/
def classical_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) : Prop := 
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F)


/-! ## D4 — Sawayama–Thébault theorem -/

/-- OWN DEFINITION. The circle `ω` (positive radius) is tangent to the line `p q`. -/
def TangentToLine (ω : Sphere Pt) (p q : Pt) : Prop :=
  0 < ω.radius ∧ Metric.infDist ω.center (line[ℝ, p, q] : Set Pt) = ω.radius

/-- OWN DEFINITION. The circle `ω` (positive radius) is internally tangent to the circle `Ω`
(lies inside `Ω` and touches it). -/
def InternallyTangent (ω Ω : Sphere Pt) : Prop :=
  0 < ω.radius ∧ ω.radius < Ω.radius ∧ dist ω.center Ω.center = Ω.radius - ω.radius

/-- D4, Sawayama–Thébault: `D` on side `BC`; `ω₁, ω₂` are tangent to lines `AD`, `BC`,
internally tangent to the circumcircle, one on each side of `AD`. Then their centres and
the incentre are collinear. -/
def classical_D4 (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    -- AMBIGUOUS: "on side BC" taken as strictly between `B` and `C` (`Wbtw` would allow
    -- `D = B` or `D = C`, where one of the two circles degenerates).
    (hd : Sbtw ℝ b d c)
    (ω₁ ω₂ : Sphere Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    TangentToLine ω₁ a d → TangentToLine ω₁ b c → InternallyTangent ω₁ t.circumsphere →
    TangentToLine ω₂ a d → TangentToLine ω₂ b c → InternallyTangent ω₂ t.circumsphere →
    (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center →
    -- EXTRA HYPOTHESIS / AMBIGUOUS: the two circles lie on the same side of `BC` as `A`
    -- (inside the angles `ADB` and `ADC`). Without it, each side of `AD` also carries a
    -- circle in the circular segment cut off by `BC`, for which the statement is not the
    -- classical one.
    (line[ℝ, b, c]).SSameSide ω₁.center a → (line[ℝ, b, c]).SSameSide ω₂.center a →
    Collinear ℝ ({ω₁.center, ω₂.center, t.incenter} : Set Pt)


/-- D4 obligation (well-formedness only): the two Thébault circles exist. -/
def classical_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a


/-! ## D5 — Kosnita's theorem -/

/-- OWN DEFINITION. `o` is equidistant from `p, q, r`, i.e. (for `p, q, r` not collinear) the
circumcentre of triangle `p q r`. -/
def IsCircumcenterOf (o p q r : Pt) : Prop :=
  dist o p = dist o q ∧ dist o p = dist o r

/-- D5, Kosnita: with `O` the circumcentre and `O_a, O_b, O_c` the circumcentres of `OBC`,
`OCA`, `OAB`, the lines `AO_a, BO_b, CO_c` are concurrent.
(If `O` lies on a side — right triangle — the corresponding `O_x` does not exist and the
statement is vacuous; see the obligation.) -/
def classical_D5 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (Oa Ob Oc : Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    IsCircumcenterOf Oa t.circumcenter b c → IsCircumcenterOf Ob t.circumcenter c a →
    IsCircumcenterOf Oc t.circumcenter a b →
    -- EXTRA HYPOTHESIS: the three lines are defined (`A ≠ O_a` etc.; `A = O_a` happens e.g.
    -- for an isosceles triangle with apex angle 120° at `A`).
    a ≠ Oa → b ≠ Ob → c ≠ Oc →
    -- AMBIGUOUS: concurrency "at infinity" allowed — the Kosnita point (isogonal conjugate
    -- of the nine-point centre) is at infinity when the nine-point centre lies on the
    -- circumcircle; then the three lines are parallel. Strict alternative: add the
    -- hypothesis that the lines are not all parallel and keep only the first disjunct.
    (∃ X : Pt, X ∈ line[ℝ, a, Oa] ∧ X ∈ line[ℝ, b, Ob] ∧ X ∈ line[ℝ, c, Oc]) ∨
      ((line[ℝ, a, Oa]).Parallel (line[ℝ, b, Ob]) ∧
        (line[ℝ, b, Ob]).Parallel (line[ℝ, c, Oc]))


/-- D5 obligation (well-formedness only): if the circumcentre is not on line `BC`, the
circumcentre of `OBC` exists. -/
def classical_D5_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ¬ Collinear ℝ ({t.circumcenter, b, c} : Set Pt) →
      ∃ Oa, IsCircumcenterOf Oa t.circumcenter b c


/-! ## D6 — Blundon's fundamental inequality -/

/-- D6, Blundon, lower bound. -/
def classical_D6_lower (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2


/-- D6, Blundon, upper bound. -/
def classical_D6_upper (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)


/-- D6 obligation (well-formedness only): the radicand is non-negative (Euler `R ≥ 2r`),
so `Real.sqrt` is the genuine square root rather than its junk value `0`. -/
def classical_D6_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius


/-! ## D7 — Steiner–Lehmus theorem -/

/-- OWN DEFINITION. `e` is the foot of the internal bisector from vertex `v` of the angle
`p v q`: `e` lies on segment `p q` and bisects the angle at `v`. -/
def IsBisectorFoot (v p q e : Pt) : Prop :=
  Wbtw ℝ p e q ∧ ∠ p v e = ∠ e v q

/-- D7, Steiner–Lehmus: if the internal bisectors from `B` and `C` (vertex to opposite side)
have equal length, then `AB = AC`. -/
def classical_D7 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (e f : Pt)
    (he : IsBisectorFoot b a c e) (hf : IsBisectorFoot c a b f)
    (hlen : dist b e = dist c f) : Prop := 
    dist a b = dist a c


/-- D7 obligation (well-formedness only): the bisector foot exists. -/
def classical_D7_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    ∃ e, IsBisectorFoot b a c e


end Fivecircles.Classical

namespace Fivecircles.Classical

noncomputable def planeIso : ℂ ≃ₗᵢ[ℝ] Pt := Complex.orthonormalBasisOneI.repr
noncomputable def complexIso : Pt ≃ₗᵢ[ℝ] ℂ := planeIso.symm

 theorem cov_cospherical_transport {s : Set Pt} :
    Cospherical (complexIso '' s) ↔ Cospherical s := by
  constructor
  · rintro ⟨o, r, hr⟩
    refine ⟨complexIso.symm o, r, fun p hp => ?_⟩
    have hh := hr (complexIso p) ⟨p, hp, rfl⟩
    rw [← complexIso.apply_symm_apply o, complexIso.dist_map] at hh
    exact hh
  · rintro ⟨o, r, hr⟩
    refine ⟨complexIso o, r, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [complexIso.dist_map]
    exact hr p hp

 theorem cov_collinear_transport {s : Set Pt} :
    Collinear ℝ (complexIso '' s) ↔ Collinear ℝ s := by
  rw [collinear_iff_exists_forall_eq_smul_vadd, collinear_iff_exists_forall_eq_smul_vadd]
  constructor
  · rintro ⟨o, v, h⟩
    refine ⟨complexIso.symm o, complexIso.symm v, fun p hp => ?_⟩
    obtain ⟨r, hr⟩ := h (complexIso p) ⟨p, hp, rfl⟩
    refine ⟨r, ?_⟩
    have hh := congrArg complexIso.symm hr
    simpa only [vadd_eq_add, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply] using hh
  · rintro ⟨o, v, h⟩
    refine ⟨complexIso o, complexIso v, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨r, rfl⟩ := h p hp
    exact ⟨r, by simp [vadd_eq_add]⟩

theorem cov_D2_part (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    (hnc : ¬ Collinear ℝ (Set.range Q))
    (hVi : Function.Injective V) (hTi : Function.Injective T) (hQi : Function.Injective Q)
    (hVT : ∀ i j, V i ≠ T j) (hVQ : ∀ i j, V i ≠ Q j) (hTQ : ∀ i j, T i ≠ Q j) :
    Cospherical (Set.range Q) := by
  have hL : ∀ i, Collinear ℝ ({V (i-1), V i, T (i+1), T (i-1)} : Set Pt) := by
    intro i
    have hh : Collinear ℝ (ℓ i : Set Pt) := by
      rw [collinear_iff_finrank_le_one]
      rw [← AffineSubspace.direction_eq_vectorSpan, hℓ i]
    apply hh.subset
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simpa using (hV (i-1)).2
    · exact (hV i).1
    · simpa using (hT (i+1)).1
    · simpa using (hT (i-1)).2
  have hC : ∀ i, Cospherical ({V (i-1), V i, T i, Q (i-1), Q i} : Set Pt) := by
    intro i
    apply (ω i).cospherical.subset
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (hω i).1
    · exact (hω i).2.1
    · exact (hω i).2.2
    · have hh := (hQ (i-1)).2.1
      rw [sub_add_cancel] at hh
      exact hh
    · exact (hQ i).1
  have res := Fivecircles.fivecircles (complexIso ∘ V) (complexIso ∘ T) (complexIso ∘ Q)
    (complexIso.injective.comp hVi) (complexIso.injective.comp hTi) (complexIso.injective.comp hQi)
    (fun i j hh => hVT i j (complexIso.injective hh))
    (fun i j hh => hVQ i j (complexIso.injective hh))
    (fun i j hh => hTQ i j (complexIso.injective hh))
    (fun i => by simpa only [Set.image_insert_eq, Set.image_singleton, Function.comp_apply]
      using (cov_collinear_transport.2 (hL i)))
    (fun i => by
      have hh := cov_cospherical_transport.2 (hC i)
      exact ⟨by simpa only [Set.image_insert_eq, Set.image_singleton, Function.comp_apply] using hh,
        coplanar_of_finrank_eq_two _ Complex.finrank_real_complex⟩)
  rcases res with hh | hh
  · apply cov_cospherical_transport.1
    simpa only [Set.range_comp] using hh.1
  · apply False.elim
    apply hnc
    apply cov_collinear_transport.1
    simpa only [Set.range_comp] using hh


/-! ## L15 gap 2: distinctness premises of `cov_D2_part` from the writer's hypotheses -/

/-- Three distinct points of a sphere are not on one line of the writer's family. -/
theorem gap_sphere_line (L : AffineSubspace ℝ Pt) (hL : Module.finrank ℝ L.direction = 1)
    (ω : Sphere Pt) (p q r : Pt) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : p ∈ ω) (hq : q ∈ ω) (hr : r ∈ ω) (hpL : p ∈ L) (hqL : q ∈ L) (hrL : r ∈ L) :
    False := by
  have hcol : Collinear ℝ (L : Set Pt) := by
    rw [collinear_iff_finrank_le_one, ← AffineSubspace.direction_eq_vectorSpan, hL]
  have hai := ω.cospherical.affineIndependent_of_mem_of_ne hp hq hr hpq hpr hqr
  rw [affineIndependent_iff_not_collinear_set] at hai
  apply hai
  apply hcol.subset
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem gap_idx_V : ∀ i j : Fin 5, i ≠ j → (j ≠ i ∧ j ≠ i + 1) ∨ (j + 1 ≠ i ∧ j + 1 ≠ i + 1) := by
  decide
theorem gap_idx_T : ∀ i j : Fin 5, i ≠ j →
    (j - 1 ≠ i - 1 ∧ j - 1 ≠ i + 1) ∨ (j + 1 ≠ i - 1 ∧ j + 1 ≠ i + 1) := by
  decide
theorem gap_idx_VT : ∀ i j : Fin 5,
    (j - 1 ≠ i ∧ j - 1 ≠ i + 1) ∨ (j + 1 ≠ i ∧ j + 1 ≠ i + 1) := by
  decide
theorem gap_idx_ne : ∀ i : Fin 5, i ≠ i + 1 ∧ i - 1 ≠ i + 1 ∧ i - 1 ≠ i := by decide

theorem gap_idx_VQ : ∀ j i : Fin 5,
    ((j = i - 1 ∨ j = i ∨ j = i + 1 ∨ j + 1 = i - 1 ∨ j + 1 = i ∨ j + 1 = i + 1) →
      (j = i - 1 ∨ j = i)) →
    ((j = i + 1 - 1 ∨ j = i + 1 ∨ j = i + 1 + 1 ∨ j + 1 = i + 1 - 1 ∨ j + 1 = i + 1 ∨
      j + 1 = i + 1 + 1) → (j = i + 1 - 1 ∨ j = i + 1)) → j ≠ i → False := by
  decide
theorem gap_idx_TQ : ∀ j i : Fin 5,
    ((j - 1 = i - 1 ∨ j - 1 = i ∨ j - 1 = i + 1 ∨ j + 1 = i - 1 ∨ j + 1 = i ∨
      j + 1 = i + 1) → j = i) →
    ((j - 1 = i + 1 - 1 ∨ j - 1 = i + 1 ∨ j - 1 = i + 1 + 1 ∨ j + 1 = i + 1 - 1 ∨
      j + 1 = i + 1 ∨ j + 1 = i + 1 + 1) → j = i + 1) → False := by
  decide

/-- All distinctness premises of `cov_D2_part` except injectivity of `Q`, derived from the
writer's hypotheses. -/
theorem gap_D2_distinct (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i) :
    Function.Injective V ∧ Function.Injective T ∧
    (∀ i j, V i ≠ T j) ∧ (∀ i j, V i ≠ Q j) ∧ (∀ i j, T i ≠ Q j) := by
  have noc : ∀ (p : Pt) a b c, a ≠ b → a ≠ c → b ≠ c → p ∈ ℓ a → p ∈ ℓ b → p ∈ ℓ c → False :=
    fun p a b c hab hac hbc ha hb hc => hconc a b c hab hac hbc ⟨p, ha, hb, hc⟩
  have hVi : Function.Injective V := by
    intro i j h
    by_contra hne
    have hj := hV j
    rw [← h] at hj
    obtain ⟨n1, -, -⟩ := gap_idx_ne i
    rcases gap_idx_V i j hne with ⟨a, b⟩ | ⟨a, b⟩
    · exact noc (V i) i (i + 1) j n1 (Ne.symm a) (Ne.symm b) (hV i).1 (hV i).2 hj.1
    · exact noc (V i) i (i + 1) (j + 1) n1 (Ne.symm a) (Ne.symm b) (hV i).1 (hV i).2 hj.2
  have hTi : Function.Injective T := by
    intro i j h
    by_contra hne
    have hj := hT j
    rw [← h] at hj
    obtain ⟨-, n2, -⟩ := gap_idx_ne i
    rcases gap_idx_T i j hne with ⟨a, b⟩ | ⟨a, b⟩
    · exact noc (T i) (i - 1) (i + 1) (j - 1) n2 (Ne.symm a) (Ne.symm b) (hT i).1 (hT i).2 hj.1
    · exact noc (T i) (i - 1) (i + 1) (j + 1) n2 (Ne.symm a) (Ne.symm b) (hT i).1 (hT i).2 hj.2
  have hVT : ∀ i j, V i ≠ T j := by
    intro i j h
    have hj := hT j
    rw [← h] at hj
    obtain ⟨n1, -, -⟩ := gap_idx_ne i
    rcases gap_idx_VT i j with ⟨a, b⟩ | ⟨a, b⟩
    · exact noc (V i) i (i + 1) (j - 1) n1 (Ne.symm a) (Ne.symm b) (hV i).1 (hV i).2 hj.1
    · exact noc (V i) i (i + 1) (j + 1) n1 (Ne.symm a) (Ne.symm b) (hV i).1 (hV i).2 hj.2
  -- the two known points of `ω k` on each of the lines `ℓ k`, `ℓ (k+1)`, `ℓ (k-1)`
  have c0 : ∀ k X, X ∈ ω k → X ∈ ℓ k → X ≠ V (k - 1) → X ≠ V k → False := by
    intro k X hX hXl h1 h2
    obtain ⟨-, -, n3⟩ := gap_idx_ne k
    have hv := (hV (k - 1)).2
    rw [sub_add_cancel] at hv
    exact gap_sphere_line (ℓ k) (hℓ k) (ω k) X (V (k - 1)) (V k) h1 h2 (hVi.ne n3)
      hX (hω k).1 (hω k).2.1 hXl hv (hV k).1
  have c1 : ∀ k X, X ∈ ω k → X ∈ ℓ (k + 1) → X ≠ V k → X ≠ T k → False := by
    intro k X hX hXl h1 h2
    exact gap_sphere_line (ℓ (k + 1)) (hℓ _) (ω k) X (V k) (T k) h1 h2 (hVT k k)
      hX (hω k).2.1 (hω k).2.2 hXl (hV k).2 (hT k).2
  have cm : ∀ k X, X ∈ ω k → X ∈ ℓ (k - 1) → X ≠ V (k - 1) → X ≠ T k → False := by
    intro k X hX hXl h1 h2
    exact gap_sphere_line (ℓ (k - 1)) (hℓ _) (ω k) X (V (k - 1)) (T k) h1 h2 (hVT _ k)
      hX (hω k).1 (hω k).2.2 hXl (hV (k - 1)).1 (hT k).1
  have memω : ∀ k X m, X ∈ ω k → X ∈ ℓ m → (m = k - 1 ∨ m = k ∨ m = k + 1) →
      X = V (k - 1) ∨ X = V k ∨ X = T k := by
    intro k X m hX hm hmk
    by_contra hh
    push Not at hh
    obtain ⟨h1, h2, h3⟩ := hh
    rcases hmk with e | e | e <;> rw [e] at hm
    · exact cm k X hX hm h1 h3
    · exact c0 k X hX hm h1 h2
    · exact c1 k X hX hm h2 h3
  have hit : ∀ k X a b, X ∈ ω k → X ∈ ℓ a → X ∈ ℓ b →
      (a = k - 1 ∨ a = k ∨ a = k + 1 ∨ b = k - 1 ∨ b = k ∨ b = k + 1) →
      X = V (k - 1) ∨ X = V k ∨ X = T k := by
    intro k X a b hX ha hb h
    rcases h with h | h | h | h | h | h
    · exact memω k X a hX ha (Or.inl h)
    · exact memω k X a hX ha (Or.inr (Or.inl h))
    · exact memω k X a hX ha (Or.inr (Or.inr h))
    · exact memω k X b hX hb (Or.inl h)
    · exact memω k X b hX hb (Or.inr (Or.inl h))
    · exact memω k X b hX hb (Or.inr (Or.inr h))
  have hVQ : ∀ i j, V i ≠ Q j := by
    intro j i h
    obtain ⟨hq1, hq2, hq3⟩ := hQ i
    rw [← h] at hq1 hq2 hq3
    have A1 : (j = i - 1 ∨ j = i ∨ j = i + 1 ∨ j + 1 = i - 1 ∨ j + 1 = i ∨ j + 1 = i + 1) →
        (j = i - 1 ∨ j = i) := by
      intro hc
      rcases hit i (V j) j (j + 1) hq1 (hV j).1 (hV j).2 hc with e | e | e
      · exact Or.inl (hVi e)
      · exact Or.inr (hVi e)
      · exact absurd e (hVT j i)
    have A2 : (j = i + 1 - 1 ∨ j = i + 1 ∨ j = i + 1 + 1 ∨ j + 1 = i + 1 - 1 ∨ j + 1 = i + 1 ∨
        j + 1 = i + 1 + 1) → (j = i + 1 - 1 ∨ j = i + 1) := by
      intro hc
      rcases hit (i + 1) (V j) j (j + 1) hq2 (hV j).1 (hV j).2 hc with e | e | e
      · exact Or.inl (hVi e)
      · exact Or.inr (hVi e)
      · exact absurd e (hVT j _)
    have A3 : j ≠ i := fun e => hq3 (by rw [e])
    clear hq1 hq2 hq3 h
    exact gap_idx_VQ j i A1 A2 A3
  have hTQ : ∀ i j, T i ≠ Q j := by
    intro j i h
    obtain ⟨hq1, hq2, hq3⟩ := hQ i
    rw [← h] at hq1 hq2 hq3
    have A1 : (j - 1 = i - 1 ∨ j - 1 = i ∨ j - 1 = i + 1 ∨ j + 1 = i - 1 ∨ j + 1 = i ∨
        j + 1 = i + 1) → j = i := by
      intro hc
      rcases hit i (T j) (j - 1) (j + 1) hq1 (hT j).1 (hT j).2 hc with e | e | e
      · exact absurd e.symm (hVT _ j)
      · exact absurd e.symm (hVT _ j)
      · exact hTi e
    have A2 : (j - 1 = i + 1 - 1 ∨ j - 1 = i + 1 ∨ j - 1 = i + 1 + 1 ∨ j + 1 = i + 1 - 1 ∨
        j + 1 = i + 1 ∨ j + 1 = i + 1 + 1) → j = i + 1 := by
      intro hc
      rcases hit (i + 1) (T j) (j - 1) (j + 1) hq2 (hT j).1 (hT j).2 hc with e | e | e
      · exact absurd e.symm (hVT _ j)
      · exact absurd e.symm (hVT _ j)
      · exact hTi e
    clear hq1 hq2 hq3 h
    exact gap_idx_TQ j i A1 A2
  exact ⟨hVi, hTi, hVT, hVQ, hTQ⟩

/-- D2 with every premise of `cov_D2_part` except injectivity of `Q` discharged. -/
theorem cov_D2_injQ (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    (hnc : ¬ Collinear ℝ (Set.range Q))
    (hQi : Function.Injective Q) :
    Cospherical (Set.range Q) := by
  obtain ⟨hVi, hTi, hVT, hVQ, hTQ⟩ := gap_D2_distinct ℓ hℓ hconc V T hV hT ω hω Q hQ
  exact cov_D2_part ℓ hℓ hpar hconc V T hV hT ω hω Q hQ hnc hVi hTi hQi hVT hVQ hTQ


/-! ### Gap 2, part B: removing injectivity of `Q`.
`gap_core_distinct` is the repository's `Fivecircles.core` proof text copied verbatim, with
the single change that injectivity of `M` is weakened to pairwise distinctness of
`M 0, M 1, M 2, M 3` (the only instances the proof uses). -/

open Fivecircles Complex ComplexConjugate in
theorem gap_core_distinct (A T M : Fin 5 → ℂ) (hA : Function.Injective A) (hT : Function.Injective T)
    (hMd : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 → M a ≠ M b) (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j)
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
  have g102 := (cd_eq_zero_iff (hA.ne (by decide : (1 : Fin 5) ≠ 2)) (hMd 1 2 (by decide) (by decide) (by decide)) (hAM 1 2) (hAM 2 1).symm).1 k101
  rw [th_sub_comm (M 1) (A 2)] at g102
  have c103 : cd (T 1) (M 3) (T 4) (M 1) = 0 := (cd_s23 (cd_s34 c94))
  have g104 := (cd_eq_zero_iff (hT.ne (by decide : (1 : Fin 5) ≠ 4)) (hMd 3 1 (by decide) (by decide) (by decide)) (hTM 1 1) (hTM 4 3).symm).1 c103
  rw [th_sub_comm (M 3) (M 1), th_sub_comm (M 3) (T 4)] at g104
  have c105 : cd (T 1) (M 3) (A 4) (M 0) = 0 := (cd_s23 (cd_s34 c88))
  have g106 := (cd_eq_zero_iff (hAT 4 1).symm (hMd 3 0 (by decide) (by decide) (by decide)) (hTM 1 0) (hAM 4 3).symm).1 c105
  rw [th_sub_comm (T 1) (A 4), th_sub_comm (M 3) (M 0), th_sub_comm (M 3) (A 4)] at g106
  have c107 : cd (A 1) (T 0) (T 3) (M 2) = 0 := (cd_s23 c76)
  have g108 := (cd_eq_zero_iff (hAT 1 3) (hTM 0 2) (hAM 1 2) (hT.ne (by decide : (0 : Fin 5) ≠ 3))).1 c107
  have c109 : cd (A 1) (M 2) (T 0) (M 0) = 0 := (cd_s23 (cd_s34 c100))
  have g110 := (cd_eq_zero_iff (hAT 1 0) (hMd 2 0 (by decide) (by decide) (by decide)) (hAM 1 0) (hTM 0 2).symm).1 c109
  rw [th_sub_comm (M 2) (M 0), th_sub_comm (M 2) (T 0)] at g110
  have z111 : th (M 0 - M 2) + th (M 1 - M 3) = th (M 0 - M 3) + th (M 1 - M 2) := by
    linear_combination (norm := abel) g2 - g6 - g28 + g50 - g12 + g16 + g62 + g64 - g66 - g54 - g68 + g70 + g80 - g58 - g32 + g34 - g36 - g102 - g44 + g24 + g104 - g106 + g108 + g110
  have c112 : cd (M 0) (M 1) (M 2) (M 3) = 0 := (cd_eq_zero_iff (hMd 0 2 (by decide) (by decide) (by decide)) (hMd 1 3 (by decide) (by decide) (by decide)) (hMd 0 3 (by decide) (by decide) (by decide)) (hMd 1 2 (by decide) (by decide) (by decide))).2 (by
    exact z111)
  exact c112


open Fivecircles Complex ComplexConjugate in
theorem gap_cd_degen (a b c d : ℂ) (h : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) :
    cd a b c d = 0 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [cd, mul_im, mul_re, sub_re, sub_im, conj_re, conj_im] <;> ring

open Fivecircles in
/-- `Fivecircles.core` without any distinctness of `M`. -/
theorem gap_core (A T M : Fin 5 → ℂ) (hA : Function.Injective A) (hT : Function.Injective T)
    (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j) (hTM : ∀ i j, T i ≠ M j)
    (hL : ∀ i, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hC : ∀ i, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ)) :
    cd (M 0) (M 1) (M 2) (M 3) = 0 := by
  by_cases hdeg : M 0 = M 1 ∨ M 0 = M 2 ∨ M 0 = M 3 ∨ M 1 = M 2 ∨ M 1 = M 3 ∨ M 2 = M 3
  · exact gap_cd_degen _ _ _ _ hdeg
  · push Not at hdeg
    obtain ⟨h01, h02, h03, h12, h13, h23⟩ := hdeg
    refine gap_core_distinct A T M hA hT ?_ hAT hAM hTM hL hC
    intro a b hab ha hb
    fin_cases a <;> fin_cases b <;> simp at hab ha hb ⊢ <;> intro e <;>
      first | exact absurd e (by assumption) | exact absurd e.symm (by assumption)

open Fivecircles in
theorem gap_cd_perms {a b c d : ℂ} (h : cd a b c d = 0) :
    cd a b c d = 0 ∧
    cd a b d c = 0 ∧
    cd a c b d = 0 ∧
    cd a c d b = 0 ∧
    cd a d b c = 0 ∧
    cd a d c b = 0 ∧
    cd b a c d = 0 ∧
    cd b a d c = 0 ∧
    cd b c a d = 0 ∧
    cd b c d a = 0 ∧
    cd b d a c = 0 ∧
    cd b d c a = 0 ∧
    cd c a b d = 0 ∧
    cd c a d b = 0 ∧
    cd c b a d = 0 ∧
    cd c b d a = 0 ∧
    cd c d a b = 0 ∧
    cd c d b a = 0 ∧
    cd d a b c = 0 ∧
    cd d a c b = 0 ∧
    cd d b a c = 0 ∧
    cd d b c a = 0 ∧
    cd d c a b = 0 ∧
    cd d c b a = 0 :=
  ⟨h,
    cd_s34 (h),
    cd_s23 (h),
    cd_s34 (cd_s23 (h)),
    cd_s23 (cd_s34 (h)),
    cd_s23 (cd_s34 (cd_s23 (h))),
    cd_s12 (h),
    cd_s34 (cd_s12 (h)),
    cd_s23 (cd_s12 (h)),
    cd_s34 (cd_s23 (cd_s12 (h))),
    cd_s23 (cd_s34 (cd_s12 (h))),
    cd_s23 (cd_s34 (cd_s23 (cd_s12 (h)))),
    cd_s12 (cd_s23 (h)),
    cd_s34 (cd_s12 (cd_s23 (h))),
    cd_s12 (cd_s23 (cd_s12 (h))),
    cd_s34 (cd_s12 (cd_s23 (cd_s12 (h)))),
    cd_s23 (cd_s34 (cd_s12 (cd_s23 (h)))),
    cd_s23 (cd_s34 (cd_s12 (cd_s23 (cd_s12 (h))))),
    cd_s12 (cd_s23 (cd_s34 (h))),
    cd_s12 (cd_s23 (cd_s34 (cd_s23 (h)))),
    cd_s12 (cd_s23 (cd_s34 (cd_s12 (h)))),
    cd_s12 (cd_s23 (cd_s34 (cd_s23 (cd_s12 (h))))),
    cd_s12 (cd_s23 (cd_s34 (cd_s12 (cd_s23 (h))))),
    cd_s12 (cd_s23 (cd_s34 (cd_s12 (cd_s23 (cd_s12 (h))))))⟩

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `0, 0`), split off to keep each proof small. -/
theorem gap_cd_all_00 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 0) (M 0) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `0, 1`), split off to keep each proof small. -/
theorem gap_cd_all_01 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 0) (M 1) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `0, 2`), split off to keep each proof small. -/
theorem gap_cd_all_02 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 0) (M 2) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `0, 3`), split off to keep each proof small. -/
theorem gap_cd_all_03 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 0) (M 3) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `0, 4`), split off to keep each proof small. -/
theorem gap_cd_all_04 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 0) (M 4) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `1, 0`), split off to keep each proof small. -/
theorem gap_cd_all_10 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 1) (M 0) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `1, 1`), split off to keep each proof small. -/
theorem gap_cd_all_11 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 1) (M 1) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `1, 2`), split off to keep each proof small. -/
theorem gap_cd_all_12 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 1) (M 2) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `1, 3`), split off to keep each proof small. -/
theorem gap_cd_all_13 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 1) (M 3) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `1, 4`), split off to keep each proof small. -/
theorem gap_cd_all_14 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 1) (M 4) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `2, 0`), split off to keep each proof small. -/
theorem gap_cd_all_20 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 2) (M 0) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `2, 1`), split off to keep each proof small. -/
theorem gap_cd_all_21 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 2) (M 1) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `2, 2`), split off to keep each proof small. -/
theorem gap_cd_all_22 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 2) (M 2) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `2, 3`), split off to keep each proof small. -/
theorem gap_cd_all_23 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 2) (M 3) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `2, 4`), split off to keep each proof small. -/
theorem gap_cd_all_24 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 2) (M 4) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `3, 0`), split off to keep each proof small. -/
theorem gap_cd_all_30 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 3) (M 0) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `3, 1`), split off to keep each proof small. -/
theorem gap_cd_all_31 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 3) (M 1) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `3, 2`), split off to keep each proof small. -/
theorem gap_cd_all_32 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 3) (M 2) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `3, 3`), split off to keep each proof small. -/
theorem gap_cd_all_33 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 3) (M 3) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `3, 4`), split off to keep each proof small. -/
theorem gap_cd_all_34 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 3) (M 4) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `4, 0`), split off to keep each proof small. -/
theorem gap_cd_all_40 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 4) (M 0) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `4, 1`), split off to keep each proof small. -/
theorem gap_cd_all_41 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 4) (M 1) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `4, 2`), split off to keep each proof small. -/
theorem gap_cd_all_42 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 4) (M 2) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `4, 3`), split off to keep each proof small. -/
theorem gap_cd_all_43 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 4) (M 3) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
/-- Part of `gap_cd_all` (first two indices `4, 4`), split off to keep each proof small. -/
theorem gap_cd_all_44 (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ c d : Fin 5, cd (M 4) (M 4) (M c) (M d) = 0 := by
  have b0 := gap_cd_perms (hb 0)
  have b1 := gap_cd_perms (hb 1)
  have b2 := gap_cd_perms (hb 2)
  have b3 := gap_cd_perms (hb 3)
  have b4 := gap_cd_perms (hb 4)
  simp only [Fin.isValue, Fin.reduceAdd, zero_add] at b0 b1 b2 b3 b4
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_11, p0_12, p0_13, p0_14, p0_15, p0_16, p0_17, p0_18, p0_19, p0_20, p0_21, p0_22, p0_23⟩ := b0
  obtain ⟨p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_14, p1_15, p1_16, p1_17, p1_18, p1_19, p1_20, p1_21, p1_22, p1_23⟩ := b1
  obtain ⟨p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9, p2_10, p2_11, p2_12, p2_13, p2_14, p2_15, p2_16, p2_17, p2_18, p2_19, p2_20, p2_21, p2_22, p2_23⟩ := b2
  obtain ⟨p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23⟩ := b3
  obtain ⟨p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9, p4_10, p4_11, p4_12, p4_13, p4_14, p4_15, p4_16, p4_17, p4_18, p4_19, p4_20, p4_21, p4_22, p4_23⟩ := b4
  intro c d
  fin_cases c <;> fin_cases d <;>
    first
    | exact gap_cd_degen _ _ _ _ (Or.inl rfl)
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inl rfl))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact gap_cd_degen _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | assumption

open Fivecircles in
theorem gap_cd_all (M : Fin 5 → ℂ)
    (hb : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0) :
    ∀ a b c d : Fin 5, cd (M a) (M b) (M c) (M d) = 0 := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact gap_cd_all_00 M hb
  · exact gap_cd_all_01 M hb
  · exact gap_cd_all_02 M hb
  · exact gap_cd_all_03 M hb
  · exact gap_cd_all_04 M hb
  · exact gap_cd_all_10 M hb
  · exact gap_cd_all_11 M hb
  · exact gap_cd_all_12 M hb
  · exact gap_cd_all_13 M hb
  · exact gap_cd_all_14 M hb
  · exact gap_cd_all_20 M hb
  · exact gap_cd_all_21 M hb
  · exact gap_cd_all_22 M hb
  · exact gap_cd_all_23 M hb
  · exact gap_cd_all_24 M hb
  · exact gap_cd_all_30 M hb
  · exact gap_cd_all_31 M hb
  · exact gap_cd_all_32 M hb
  · exact gap_cd_all_33 M hb
  · exact gap_cd_all_34 M hb
  · exact gap_cd_all_40 M hb
  · exact gap_cd_all_41 M hb
  · exact gap_cd_all_42 M hb
  · exact gap_cd_all_43 M hb
  · exact gap_cd_all_44 M hb

open Fivecircles in
/-- Repository `fivecircles` without injectivity of `M`, under non-collinearity. -/
theorem gap_fivecircles (A T M : Fin 5 → ℂ) (hA : Function.Injective A)
    (hT : Function.Injective T) (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j)
    (hTM : ∀ i j, T i ≠ M j)
    (hL : ∀ i, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hC : ∀ i, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ))
    (hnc : ¬ Collinear ℝ (Set.range M)) :
    Concyclic (Set.range M) := by
  have sh : ∀ k : Fin 5, cd (M k) (M (k + 1)) (M (k + 2)) (M (k + 3)) = 0 := by
    intro k
    have := gap_core (fun i => A (i + k)) (fun i => T (i + k)) (fun i => M (i + k))
      (fun i j h => add_right_cancel (hA h)) (fun i j h => add_right_cancel (hT h))
      (fun i j => hAT _ _) (fun i j => hAM _ _)
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
  have hall := gap_cd_all M sh
  have hex : ∃ i j k, col3 (M k) (M j) (M i) ≠ 0 := by
    by_contra H
    push Not at H
    apply hnc
    by_cases hj : ∃ j, M j ≠ M 0
    · obtain ⟨j, hj⟩ := hj
      exact collinear_of ⟨0, rfl⟩ (Ne.symm hj) (by rintro _ ⟨m, rfl⟩; exact H 0 j m)
    · push Not at hj
      have : Set.range M = {M 0} := by
        ext x; simp only [Set.mem_range, Set.mem_singleton_iff]
        constructor
        · rintro ⟨m, rfl⟩; exact hj m
        · rintro rfl; exact ⟨0, rfl⟩
      rw [this]; exact collinear_singleton _ _
  obtain ⟨i, j, k, hD⟩ := hex
  exact concyclic_of hD (by rintro _ ⟨m, rfl⟩; exact hall i j k m)

/-- **D2, exact writer statement.** -/
theorem cov_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    -- The classical statement presupposes a second point; AMBIGUOUS: if `ω i, ω (i+1)` are
    -- tangent at `V i` one could take `Q i = V i` (here such configurations are excluded by
    -- the requirement `Q i ≠ V i`).
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical ∨ Collinear` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range Q)) :
    Cospherical (Set.range Q) := by
  obtain ⟨hVi, hTi, hVT, hVQ, hTQ⟩ := gap_D2_distinct ℓ hℓ hconc V T hV hT ω hω Q hQ
  have hL : ∀ i, Collinear ℝ ({V (i-1), V i, T (i+1), T (i-1)} : Set Pt) := by
    intro i
    have hh : Collinear ℝ (ℓ i : Set Pt) := by
      rw [collinear_iff_finrank_le_one]
      rw [← AffineSubspace.direction_eq_vectorSpan, hℓ i]
    apply hh.subset
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simpa using (hV (i-1)).2
    · exact (hV i).1
    · simpa using (hT (i+1)).1
    · simpa using (hT (i-1)).2
  have hC : ∀ i, Cospherical ({V (i-1), V i, T i, Q (i-1), Q i} : Set Pt) := by
    intro i
    apply (ω i).cospherical.subset
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (hω i).1
    · exact (hω i).2.1
    · exact (hω i).2.2
    · have hh := (hQ (i-1)).2.1
      rw [sub_add_cancel] at hh
      exact hh
    · exact (hQ i).1
  have res := gap_fivecircles (complexIso ∘ V) (complexIso ∘ T) (complexIso ∘ Q)
    (complexIso.injective.comp hVi) (complexIso.injective.comp hTi)
    (fun i j hh => hVT i j (complexIso.injective hh))
    (fun i j hh => hVQ i j (complexIso.injective hh))
    (fun i j hh => hTQ i j (complexIso.injective hh))
    (fun i => by simpa only [Set.image_insert_eq, Set.image_singleton, Function.comp_apply]
      using (cov_collinear_transport.2 (hL i)))
    (fun i => by
      have hh := cov_cospherical_transport.2 (hC i)
      exact ⟨by simpa only [Set.image_insert_eq, Set.image_singleton, Function.comp_apply] using hh,
        coplanar_of_finrank_eq_two _ Complex.finrank_real_complex⟩)
    (by
      intro hh; apply hnc; apply cov_collinear_transport.1
      simpa only [Set.range_comp] using hh)
  apply cov_cospherical_transport.1
  simpa only [Set.range_comp] using res.1

theorem cov_D2_exact (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt) (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i) (Q : Fin 5 → Pt)
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i) (hnc : ¬ Collinear ℝ (Set.range Q)) :
    classical_D2 ℓ hℓ hpar hconc V T hV hT ω hω Q hQ hnc :=
  cov_D2 ℓ hℓ hpar hconc V T hV hT ω hω Q hQ hnc


/-! ## L15 gap 4 (D2 part): the D2 construction obligation -/

theorem gap_line_ne_bot (L : AffineSubspace ℝ Pt) (hL : Module.finrank ℝ L.direction = 1) :
    L ≠ ⊥ := by
  rintro rfl
  rw [AffineSubspace.direction_bot, finrank_bot] at hL
  exact zero_ne_one hL

/-- Two non-parallel lines of the plane meet. -/
theorem gap_lines_meet (L₁ L₂ : AffineSubspace ℝ Pt)
    (h₁ : Module.finrank ℝ L₁.direction = 1) (h₂ : Module.finrank ℝ L₂.direction = 1)
    (hp : ¬ L₁.Parallel L₂) : ∃ p, p ∈ L₁ ∧ p ∈ L₂ := by
  have n₁ := gap_line_ne_bot L₁ h₁
  have n₂ := gap_line_ne_bot L₂ h₂
  have hd : L₁.direction ≠ L₂.direction := by
    intro he
    exact hp (AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot.2
      ⟨he, ⟨fun h => absurd h n₁, fun h => absurd h n₂⟩⟩)
  have key := Submodule.finrank_sup_add_finrank_inf_eq L₁.direction L₂.direction
  rw [h₁, h₂] at key
  have hinf : Module.finrank ℝ ↥(L₁.direction ⊓ L₂.direction) = 0 := by
    have hle : Module.finrank ℝ ↥(L₁.direction ⊓ L₂.direction) ≤ 1 := by
      rw [← h₁]; exact Submodule.finrank_mono inf_le_left
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
    · exact h0
    · exfalso
      apply hd
      have e1 := Submodule.eq_of_le_of_finrank_eq inf_le_left (h1.trans h₁.symm)
      have e2 := Submodule.eq_of_le_of_finrank_eq inf_le_right (h1.trans h₂.symm)
      exact e1.symm.trans e2
  have hsup : L₁.direction ⊔ L₂.direction = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_top, finrank_euclideanSpace_fin]
    omega
  obtain ⟨p, hp1, hp2⟩ := AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
    ((AffineSubspace.nonempty_iff_ne_bot _).2 n₁) ((AffineSubspace.nonempty_iff_ne_bot _).2 n₂) hsup
  exact ⟨p, hp1, hp2⟩

theorem gap_idx_obl : ∀ i : Fin 5, i - 1 ≠ i ∧ i - 1 ≠ i + 1 ∧ i ≠ i + 1 ∧ i - 1 + 1 = i := by
  decide

/-- **D2 obligation, exact writer statement.** -/
theorem cov_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) :
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt) := by
  have hV : ∀ i : Fin 5, ∃ p, p ∈ ℓ i ∧ p ∈ ℓ (i + 1) := fun i =>
    gap_lines_meet _ _ (hℓ _) (hℓ _) (hpar _ _ (gap_idx_obl i).2.2.1)
  have hT : ∀ i : Fin 5, ∃ p, p ∈ ℓ (i - 1) ∧ p ∈ ℓ (i + 1) := fun i =>
    gap_lines_meet _ _ (hℓ _) (hℓ _) (hpar _ _ (gap_idx_obl i).2.1)
  choose V hV using hV
  choose T hT using hT
  refine ⟨V, T, hV, hT, fun i hcol => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := gap_idx_obl i
  have hv1 : V (i - 1) ∈ ℓ (i - 1) := (hV (i - 1)).1
  have hv2 : V (i - 1) ∈ ℓ i := by have := (hV (i - 1)).2; rwa [a4] at this
  have hne : V (i - 1) ≠ V i := by
    intro he
    exact hconc (i - 1) i (i + 1) a1 a2 a3 ⟨V i, he ▸ hv1, (hV i).1, (hV i).2⟩
  have hmem : T i ∈ line[ℝ, V (i - 1), V i] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne
  have hle : line[ℝ, V (i - 1), V i] ≤ ℓ i := by
    apply affineSpan_le.2
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact hv2
    · exact (hV i).1
  exact hconc (i - 1) i (i + 1) a1 a2 a3 ⟨T i, (hT i).1, hle hmem, (hT i).2⟩

theorem cov_D2_obligation_exact (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) :
    classical_D2_obligation ℓ hℓ hpar hconc :=
  cov_D2_obligation ℓ hℓ hpar hconc

end Fivecircles.Classical
