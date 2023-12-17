import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Position.Orientation

/-!
# Quadrilateral

In this file we define general quadrilaterals as four points on the plane and convex quadrilaterals.

## Important Definitions
* `Quadrilateral P` : general quadrilaterals on the plane `P`, i.e. four points on `P`
* `Quadrilateral_nd P` : quadrilaterals on the plane `P` s.t. the points that adjacent is not same
* `Quadrilateral_cvx P` : convex quadrilaterals on the plane `P`

## Notation
* `QDR A B C D` : notation for quadrilateral `A B C D`

## Implementation Notes
Currently, we just defines general quadrilaterals, non-degenerate quadrilateral (adjacent points are not the same, or cyclic-non-degenerate) and convex quadrilaterals.
There are classes in between. For example, quadrilateral without self-intersection, quadrilateral of stronger non-degenerate (any two points are not same, we call it alternatively-non-degenerate temporarily).
Of course many definitions work on these classes already, but without necessarity in application, we will not formalize these class for present.
-/

noncomputable section
namespace EuclidGeom

/-- Class of Quadrilateral: A quadrilateral consists of four points; it is the generalized quadrilateral formed by these four points -/
@[ext]
structure Quadrilateral (P : Type _) [EuclideanPlane P] where
  point₁ : P
  point₂ : P
  point₃ : P
  point₄ : P

/-- For four points $A$ $B$ $C$ $D$ on a plane, instead of writing Quadrilateral.mk $A$ $B$ $C$ $D$ for the quadrilateral formed by $A$ $B$ $C$ $D$, we use QDR $A$ $B$ $C$ $D$ to denote such a quadrilateral. -/
scoped notation "QDR" => Quadrilateral.mk

namespace Quadrilateral
variable {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P}

/-- Given a quadrilateral qdr, qdr.edge₁₂ is the edge from the first point to the second point of a quadrilateral. -/
@[pp_dot]
def edge₁₂ : Seg P := SEG qdr.1 qdr.2

/-- The edge from the second point to the third point of a quadrilateral -/
@[pp_dot]
def edge₂₃ : Seg P := SEG qdr.2 qdr.3

/-- The edge from the third point to the fourth point of a quadrilateral -/
@[pp_dot]
def edge₃₄ : Seg P := SEG qdr.3 qdr.4

/-- The edge from the 1st point to the 4th point of a quadrilateral -/
@[pp_dot]
def edge₁₄ : Seg P := SEG qdr.1 qdr.4

/-- The diagonal from the first point to the third point of a quadrilateral -/
@[pp_dot]
def diag₁₃ : Seg P := SEG qdr.1 qdr.3

/-- The diagonal from the second point to the fourth point of a quadrilateral -/
@[pp_dot]
def diag₂₄ : Seg P := SEG qdr.2 qdr.4

/-- The permute quadrilateral, the first point of the permute is the second point of the origin, etc. -/
@[pp_dot]
def permute : Quadrilateral P := QDR qdr.2 qdr.3 qdr.4 qdr.1

/-- The reflect quadrilateral, exchanged the second point and the fourth. -/
@[pp_dot]
def reflect : Quadrilateral P := QDR qdr.1 qdr.4 qdr.3 qdr.2

end Quadrilateral

/--
A quadrilateral is called non-degenerate if the points that adjacent is not same
-/
@[pp_dot]
structure Quadrilateral.IsND {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop where
  nd₁₂ : (qdr.2 ≠ qdr.1)
  nd₂₃ : (qdr.3 ≠ qdr.2)
  nd₃₄ : (qdr.4 ≠ qdr.3)
  nd₁₄ : (qdr.4 ≠ qdr.1)

/--
Class of nd Quadrilateral: A nd quadrilateral is quadrilateral with the property of nd.
-/
@[ext]
structure Quadrilateral_nd (P : Type _) [EuclideanPlane P] extends Quadrilateral P where
  nd : toQuadrilateral.IsND

def Quadrilateral_nd.mk_pt_pt_pt_pt_nd {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) : Quadrilateral_nd P where
  toQuadrilateral := (QDR A B C D)
  nd := h

scoped notation "QDR_nd" => Quadrilateral_nd.mk_pt_pt_pt_pt_nd

namespace Quadrilateral_nd

/-- Given a property that a quadrilateral qdr is nd, this function returns qdr itself as an object in the class of nd quadrilateral -/
def mk_is_nd {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr.IsND) : Quadrilateral_nd P where
  toQuadrilateral := qdr
  nd := h

section property_nd
-- properties of nd quadrilateral `to be added`

variable {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P)

/-- The edge from the first point to the second point of a quadrilateral_nd is non-degenerate. -/
theorem nd₁₂ :  qdr_nd.1.2 ≠ qdr_nd.1.1 := qdr_nd.nd.nd₁₂

/-- The edge from the first point to the second point of a quadrilateral_nd is non-degenerate. -/
theorem nd₂₃ :  qdr_nd.1.3 ≠ qdr_nd.1.2 := qdr_nd.nd.nd₂₃

/-- The edge from the first point to the second point of a quadrilateral_nd is non-degenerate. -/
theorem nd₃₄ :  qdr_nd.1.4 ≠ qdr_nd.1.3 := qdr_nd.nd.nd₃₄

/-- The edge from the first point to the second point of a quadrilateral_nd is non-degenerate. -/
theorem nd₁₄ :  qdr_nd.1.4 ≠ qdr_nd.1.1 := qdr_nd.nd.nd₁₄

/-- The edge from the first point to the second point of a quadrilateral -/
@[pp_dot]
def edge_nd₁₂ : SegND P := SEG_nd qdr_nd.point₁ qdr_nd.point₂ (qdr_nd.nd₁₂)

/-- The edge from the second point to the third point of a quadrilateral -/
@[pp_dot]
def edge_nd₂₃ : SegND P := SEG_nd qdr_nd.point₂ qdr_nd.point₃ (qdr_nd.nd₂₃)

/-- The edge from the third point to the fourth point of a quadrilateral -/
@[pp_dot]
def edge_nd₃₄ : SegND P := SEG_nd qdr_nd.point₃ qdr_nd.point₄ (qdr_nd.nd₃₄)

/-- The edge from the fourth point to the first point of a quadrilateral -/
@[pp_dot]
def edge_nd₁₄ : SegND P := SEG_nd qdr_nd.point₁ qdr_nd.point₄ (qdr_nd.nd₁₄)

/--angle at point₁ of qdr_nd-/
@[pp_dot]
def angle₁ : Angle P := ANG qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂ qdr_nd.nd₁₄ qdr_nd.nd₁₂

/--angle at point₂ of qdr_nd-/
@[pp_dot]
def angle₂ : Angle P := ANG qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃ qdr_nd.nd₁₂.symm qdr_nd.nd₂₃

/--angle at point₃ of qdr_nd-/
@[pp_dot]
def angle₃ : Angle P := ANG qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄ qdr_nd.nd₂₃.symm qdr_nd.nd₃₄

/--angle at point₄ of qdr_nd-/
@[pp_dot]
def angle₄ : Angle P := ANG qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁ qdr_nd.nd₃₄.symm qdr_nd.nd₁₄.symm

/--triangle point₄ point₁ point₂, which includes angle₁-/
@[pp_dot]
def triangle₁ : Triangle P := TRI qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂

/--triangle point₁ point₂ point₃, which includes angle₂-/
@[pp_dot]
def triangle₂ : Triangle P := TRI qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃

/--triangle point₂ point₃ point₄, which includes angle₃-/
@[pp_dot]
def triangle₃ : Triangle P := TRI qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄

/--triangle point₃ point₄ point₁, which includes angle₄-/
@[pp_dot]
def triangle₄ : Triangle P := TRI qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁

/-- The permute of quadrilateral_nd is also quadrilateral_nd. -/
theorem permute_is_nd : (qdr_nd.1.permute).IsND := by
  constructor
  exact qdr_nd.nd₂₃
  exact qdr_nd.nd₃₄
  exact qdr_nd.nd₁₄.symm
  exact qdr_nd.nd₁₂.symm

/-- The permute quadrilateral_nd, the first point of the permute is the second point of the origin, etc. -/
@[pp_dot]
def permute : Quadrilateral_nd P := mk_is_nd (permute_is_nd qdr_nd)

/-- The reflect of quadrilateral_nd is also quadrilateral_nd. -/
theorem reflect_is_nd : (qdr_nd.1.reflect).IsND := by
  constructor
  exact qdr_nd.nd₁₄
  exact qdr_nd.nd₃₄.symm
  exact qdr_nd.nd₂₃.symm
  exact qdr_nd.nd₁₂

/-- The reflect quadrilateral_nd, exchanged the second point and the fourth. -/
@[pp_dot]
def reflect : Quadrilateral_nd P := mk_is_nd (reflect_is_nd qdr_nd)

end property_nd

end Quadrilateral_nd

/--
A quadrilateral_nd is called convex if four angles are same sign.
-/
@[pp_dot]
def Quadrilateral_nd.IsConvex {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop := (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₃.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)

scoped postfix : 50 "IsConvex" => Quadrilateral_nd.IsConvex

@[pp_dot]
def Quadrilateral.IsConvex {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr.IsND
  · exact (Quadrilateral_nd.mk_is_nd h).IsConvex
  · exact False

scoped postfix : 50 "IsConvex" => Quadrilateral.IsConvex

/--
Class of Convex Quadrilateral: A convex quadrilateral is quadrilateral with the property of convex.
-/
@[ext]
structure Quadrilateral_cvx (P : Type _) [EuclideanPlane P] extends Quadrilateral_nd P where
  convex : toQuadrilateral_nd IsConvex

def Quadrilateral_cvx.mk_pt_pt_pt_pt_convex {P : Type _} [EuclideanPlane P] (A B C D : P) (g : (QDR A B C D).IsND) (h : (QDR_nd A B C D g) IsConvex): Quadrilateral_cvx P where
  toQuadrilateral := (QDR A B C D)
  nd := g
  convex := h

scoped notation "QDR_cvx" => Quadrilateral_cvx.mk_pt_pt_pt_pt_convex

namespace Quadrilateral_cvx

/-- Given a property that a quadrilateral qdr is convex, this function returns qdr itself as an object in the class of convex quadrilateral-/
def mk_is_convex {P : Type _} [EuclideanPlane P] {qdr_nd : Quadrilateral_nd P} (h : qdr_nd IsConvex) : Quadrilateral_cvx P where
  toQuadrilateral := qdr_nd.toQuadrilateral
  nd := qdr_nd.nd
  convex := h

section criteria_cvx
variable {P : Type _} [EuclideanPlane P] {A B C D : P}

structure is_convex_of_three_sides_two_pts_at_same_side' where
  qdr_nd : Quadrilateral_nd P
  same_side₁ : odist_sign qdr_nd.point₁ qdr_nd.edge_nd₃₄ = odist_sign qdr_nd.point₂ qdr_nd.edge_nd₃₄
  same_side₂ : odist_sign qdr_nd.point₂ qdr_nd.edge_nd₁₄.reverse = odist_sign qdr_nd.point₃ qdr_nd.edge_nd₁₄.reverse
  same_side₃ : odist_sign qdr_nd.point₃ qdr_nd.edge_nd₁₂ = odist_sign qdr_nd.point₄ qdr_nd.edge_nd₁₂

/- Given Quadrilateral_nd qdr_nd, if qdr_nd.point₁ and qdr_nd.point₂ are at the same side of qdr_nd.nd₃₄, and it also holds for nd₄₁ and nd₁₂, then it's convex. -/
theorem is_convex_of_three_sides_two_pts_at_same_side (p : is_convex_of_three_sides_two_pts_at_same_side' (P := P)) : p.qdr_nd IsConvex := by
  let qdr_nd := p.qdr_nd
  sorry
  -- by_cases h : odist_sign qdr_nd.point₁ qdr_nd.edge_nd₃₄ = 1
  -- ·

structure is_convex_of_diag_inx_lies_int' where
  qdr : Quadrilateral P
  ne₁ : qdr.point₁ ≠ qdr.point₃
  ne₂ : qdr.point₂ ≠ qdr.point₄
  diag₁₃ := (SEG_nd qdr.point₁ qdr.point₃ ne₁.symm)
  diag₂₄ := (SEG_nd qdr.point₂ qdr.point₄ ne₂.symm)
  not_para : ¬ diag₁₃ ∥ diag₂₄
  -- inx := LineInx diag₁₃.toLine diag₂₄.toLine not_para
  inx_lies_int₁ : LineInx diag₁₃.toLine diag₂₄.toLine not_para LiesInt diag₁₃
  inx_lies_int₂ : LineInx diag₁₃.toLine diag₂₄.toLine not_para LiesInt diag₂₄

/- Given Quadrilateral qdr, two diagonals intersect in their interior, then qdr is a Quadrilateral_cvx. -/
theorem is_convex_of_diag_inx_lies_int (p : is_convex_of_diag_inx_lies_int' (P := P)) : p.qdr IsConvex := by sorry
  /-
  1. proof it's nd.
  2. proof it's satisfy is_convex_of_three_sides_two_pts_at_same_side.
  3. proof sign of angle₁ = angle₃, angle₂ = angle₄.
  4. because nd₂₃ not divid pt₁ and pt₄, then sign of angle₂ = angle₃.
  -/

-- theorem is_convex_of four inferior angle
-- theorem is_convex_of both diag divids other pts
-- `to be added`

end criteria_cvx

section property_cvx
-- properties of convex quadrilateral `to be added`

variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)

/-- The permute of quadrilateral_cvx is also quadrilateral_cvx. -/
theorem permute_is_convex : qdr_cvx.1.permute IsConvex := by
  unfold Quadrilateral_nd.IsConvex
  by_cases h : (qdr_cvx.angle₁.value.IsPos ∧ qdr_cvx.angle₂.value.IsPos ∧ qdr_cvx.angle₃.value.IsPos ∧ qdr_cvx.angle₄.value.IsPos)
  · have q : (qdr_cvx.permute.angle₄.value.IsPos ∧ qdr_cvx.permute.angle₁.value.IsPos ∧ qdr_cvx.permute.angle₂.value.IsPos ∧ qdr_cvx.permute.angle₃.value.IsPos) := by
      exact h
    simp only [q, and_self, true_or]
  · have p: qdr_cvx.IsConvex := qdr_cvx.convex
    unfold Quadrilateral_nd.IsConvex at p
    simp only [h, false_or] at p
    have q : (qdr_cvx.permute.angle₄.value.IsNeg ∧ qdr_cvx.permute.angle₁.value.IsNeg ∧ qdr_cvx.permute.angle₂.value.IsNeg ∧ qdr_cvx.permute.angle₃.value.IsNeg) := by
      exact p
    simp only [q, and_self, or_true]
  -- unfold Quadrilateral.IsConvex
  -- have k : (QDR qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁).IsND := (Quadrilateral_nd.permute_is_nd qdr_cvx.toQuadrilateral_nd)
  -- have h : qdr_cvx.point₂ ≠ qdr_cvx.point₄ ∧ qdr_cvx.point₃ ≠ qdr_cvx.point₁ := ⟨qdr_cvx.nd₂₄.symm, qdr_cvx.nd₁₃⟩
  -- simp only [k, ne_eq, h, not_false_eq_true, and_self, dite_true]
  -- have g: ¬ qdr_cvx.diag_nd₁₃ ∥ qdr_cvx.diag_nd₂₄ := qdr_cvx.diag_not_para
  -- rw [diag_nd₁₃, diag_nd₂₄] at g
  -- have g': ¬ (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ h.2.symm) ∥ (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ h.1.symm) := by
  --   apply Ne.symm (Seg_nd.not_para_rev_of_not_para (Ne.symm g))
  -- simp only [k, g', not_false_eq_true, dite_true]
  -- have g'': ¬ (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ h.1.symm) ∥ (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ h.2.symm) := Ne.symm g'
  -- have nd₃₁_eq_nd₁₃ : (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.nd₁₃.symm).toLine = (SEG_nd qdr_cvx.point₁ qdr_cvx.point₃ qdr_cvx.nd₁₃).toLine := by
  --   exact (Line.line_of_pt_pt_eq_rev qdr_cvx.nd₁₃.symm)
  -- have inx_eq : qdr_cvx.diag_inx = LineInx (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).toLine (SEG_nd qdr_cvx.point₁ qdr_cvx.point₃ qdr_cvx.nd₁₃).toLine (Ne.symm qdr_cvx.diag_not_para) := Eq.symm (Line.inx.symm (Seg_nd.not_para_toline_of_not_para qdr_cvx.diag_nd₁₃ qdr_cvx.diag_nd₂₄ qdr_cvx.diag_not_para))
  -- rcases qdr_cvx.diag_inx_lies_int with ⟨a, b⟩
  -- have inx_eq' : qdr_cvx.diag_inx = Line.inx (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).toLine (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.nd₁₃.symm).toLine g'':= by
  --   rw [inx_eq]
  --   congr 1
  --   exact nd₃₁_eq_nd₁₃.symm
  -- rw [←inx_eq']
  -- exact ⟨b, (Seg.lies_int_rev_iff_lies_int.mp a)⟩

/-- The permute quadrilateral_cvx, the first point of the permute is the second point of the origin, etc. -/
def permute : Quadrilateral_cvx P := mk_is_convex (permute_is_convex qdr_cvx)

/-- The reflect of quadrilateral_cvx is also quadrilateral_cvx. -/
theorem reflect_is_convex : qdr_cvx.1.reflect IsConvex := by
  unfold Quadrilateral_nd.IsConvex
  have h₁ : qdr_cvx.point₁ = qdr_cvx.1.reflect.point₁ := by
    sorry
  have g₁ : qdr_cvx.angle₁.value.IsPos ↔ qdr_cvx.1.reflect.angle₁.value.IsNeg := by
    unfold Quadrilateral_nd.angle₁ Quadrilateral_nd.reflect
    sorry
  by_cases h : (qdr_cvx.angle₁.value.IsPos ∧ qdr_cvx.angle₂.value.IsPos ∧ qdr_cvx.angle₃.value.IsPos ∧ qdr_cvx.angle₄.value.IsPos)
  · have q : (qdr_cvx.reflect.angle₁.value.IsNeg ∧ qdr_cvx.reflect.angle₄.value.IsNeg ∧ qdr_cvx.reflect.angle₃.value.IsNeg ∧ qdr_cvx.reflect.angle₂.value.IsNeg) := by
      sorry
    simp only [q, and_self, or_true]
  · have p: qdr_cvx.IsConvex := qdr_cvx.convex
    unfold Quadrilateral_nd.IsConvex at p
    simp only [h, false_or] at p
    have q : (qdr_cvx.reflect.angle₁.value.IsPos ∧ qdr_cvx.reflect.angle₄.value.IsPos ∧ qdr_cvx.reflect.angle₃.value.IsPos ∧ qdr_cvx.reflect.angle₂.value.IsPos) := by
      sorry
    simp only [q, and_self, true_or]

/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₁₃ : qdr_cvx.point₃ ≠ qdr_cvx.point₁ := by
  by_contra h
  have g : qdr_cvx.angle₂.value = 0 := by
    unfold Quadrilateral_nd.angle₂
    simp only [h]
    exact angle_eq_zero_of_same_dir
  have k₁ : ¬ qdr_cvx.angle₂.value.IsPos := by
    rw [g]
    exact AngValue.zero_not_isPos
  have k₂ : ¬ qdr_cvx.angle₂.value.IsNeg := by
    rw [g]
    exact AngValue.zero_not_isNeg
  have p: qdr_cvx.IsConvex := qdr_cvx.convex
  unfold Quadrilateral_nd.IsConvex at p
  simp only [k₁, false_and, and_false, k₂, or_self] at p
  -- have h: qdr_cvx.IsConvex := qdr_cvx.convex
  -- unfold Quadrilateral_nd.IsConvex at h
  -- by_cases k: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄
  -- exact k.left.symm
  -- simp only [k, dite_false] at h

/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₂₄ : qdr_cvx.point₄ ≠ qdr_cvx.point₂ := (qdr_cvx.permute).nd₁₃

/-- The non-degenerate diagonal from the first point and third point of a convex quadrilateral -/
def diag_nd₁₃ : SegND P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₃ qdr_cvx.nd₁₃

/-- The non-degenerate diagonal from the second point and fourth point of a convex quadrilateral -/
def diag_nd₂₄ : SegND P := SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄

/-- Two diagonals are not parallel to each other -/
theorem diag_not_para : ¬ qdr_cvx.diag_nd₁₃ ∥ qdr_cvx.diag_nd₂₄ := by
  sorry
  -- have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
  -- have k: qdr_cvx.IsConvex := qdr_cvx.convex
  -- unfold Quadrilateral_nd.IsConvex at k
  -- simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
  -- by_contra q
  -- have r: qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := by exact q.symm
  -- rw [diag_nd₁₃, diag_nd₂₄] at r
  -- simp [r] at k

/-- The intersection point of two diagonals -/
@[pp_dot]
def diag_inx : P := Line.inx qdr_cvx.diag_nd₁₃.toLine qdr_cvx.diag_nd₂₄.toLine qdr_cvx.diag_not_para

/-- The interior of two diagonals intersect at one point, i.e. the intersection point of the underlying lines of the diagonals lies in the interior of both diagonals. -/
theorem diag_inx_lies_int : qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₁₃.1 ∧ qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₂₄.1
:= by sorry
  -- have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
  -- have k: qdr_cvx.IsConvex := qdr_cvx.convex
  -- unfold Quadrilateral_nd.IsConvex at k
  -- simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
  -- have g: ¬ qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := Ne.symm qdr_cvx.diag_not_para
  -- rw [diag_nd₁₃, diag_nd₂₄] at g
  -- simp only [g, dite_true] at k
  -- exact k

-- Given a convex quadrilateral qdr_cvx, edge from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point.
-- not used because changing of definition.
-- theorem nd₁₂ : qdr_cvx.point₂ ≠ qdr_cvx.point₁ := by
--   have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
--   have k: qdr_cvx.IsConvex := qdr_cvx.convex
--   unfold Quadrilateral_nd.IsConvex at k
--   simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
--   have g: ¬ qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := Ne.symm qdr_cvx.diag_not_para
--   rw [diag_nd₁₃, diag_nd₂₄] at g
--   simp only [g, dite_true] at k
--   by_contra q
--   have point₁_lieson_diag_nd₁₃: qdr_cvx.point₁ LiesOn qdr_cvx.diag_nd₁₃ := qdr_cvx.diag_nd₁₃.source_lies_on
--   have point₁_lieson_diag_nd₂₄: qdr_cvx.point₁ LiesOn qdr_cvx.diag_nd₂₄ := by
--     rw [←q]
--     exact qdr_cvx.diag_nd₂₄.source_lies_on
--   have s: qdr_cvx.point₁ IsInxOf qdr_cvx.diag_nd₁₃.toLine qdr_cvx.diag_nd₂₄.toLine := ⟨seg_lies_on_line point₁_lieson_diag_nd₁₃, seg_lies_on_line point₁_lieson_diag_nd₂₄⟩
--   have t: qdr_cvx.diag_inx = qdr_cvx.point₁ := unique_of_inx_of_line_of_not_para qdr_cvx.diag_not_para s (Line.inx_is_inx qdr_cvx.diag_not_para (l₁ := qdr_cvx.diag_nd₁₃.toLine) (l₂ := qdr_cvx.diag_nd₂₄.toLine))
--   have point₁_lies_int_diag_nd₁₃: qdr_cvx.point₁ LiesInt qdr_cvx.diag_nd₁₃ := by
--     rw [←t]
--     exact qdr_cvx.diag_inx_lies_int.1
--   have point₁_not_lies_int_diag_nd₁₃: ¬ qdr_cvx.point₁ LiesInt qdr_cvx.diag_nd₁₃ := qdr_cvx.diag_nd₁₃.source_not_lies_int
--   exact point₁_not_lies_int_diag_nd₁₃ point₁_lies_int_diag_nd₁₃

/-- Given a convex quadrilateral qdr_cvx, its 1st, 2nd and 3rd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₁ point₂}$ is not the same as the projective direction of the vector $\overrightarrow{point₁ point₃}$. -/
theorem not_colinear₁₂₃ : ¬ colinear qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 2nd, 3rd and 4th points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₂ point₃}$ is not the same as the projective direction of the vector $\overrightarrow{point₂ point₄}$. -/
theorem not_colinear₂₃₄ : ¬ colinear qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 3rd, 4th and 1st points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₃₄₁ : ¬ colinear qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 1st and 3rd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₄₁₃ : ¬ colinear qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₃ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 3rd and 1st points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₄₃₁ : ¬ colinear qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 4th and 3rd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₁₄₃ : ¬ colinear qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.point₃ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 1st and 2nd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₄₁₂ : ¬ colinear qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 2nd, 1st and 4th points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₂₁₄ : ¬ colinear qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 4th and 2nd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₁₄₂ : ¬ colinear qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.point₂ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 2nd and 4th points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₁₂₄ : ¬ colinear qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ := sorry

-- We need to add a bunch of such theorems as they may be useful in discussing general quadrilaterals, i.e. not convex, even as contradictory in proofs.

/--triangle point₄ point₁ point₂, which includes angle₁-/
@[pp_dot]
def triangle_nd₁ : TriangleND P := ⟨qdr_cvx.triangle₁,qdr_cvx.not_colinear₄₁₂⟩

/--triangle point₁ point₂ point₃, which includes angle₂-/
@[pp_dot]
def triangle_nd₂ : TriangleND P := ⟨qdr_cvx.triangle₂,qdr_cvx.not_colinear₁₂₃⟩

/--triangle point₂ point₃ point₄, which includes angle₃-/
@[pp_dot]
def triangle_nd₃ : TriangleND P := ⟨qdr_cvx.triangle₃,qdr_cvx.not_colinear₂₃₄⟩

/--triangle point₃ point₄ point₁, which includes angle₄-/
@[pp_dot]
def triangle_nd₄ : TriangleND P := ⟨qdr_cvx.triangle₄,qdr_cvx.not_colinear₃₄₁⟩

theorem cclock_eq : qdr_cvx.triangle_nd₁.is_cclock ↔ qdr_cvx.triangle_nd₃.is_cclock := sorry

theorem cclock_eq' : qdr_cvx.triangle_nd₂.is_cclock ↔ qdr_cvx.triangle_nd₄.is_cclock := sorry

end property_cvx

end Quadrilateral_cvx

section criteria
-- the criteria of a quadrilateral being convex `to be added`

variable {P : Type _} [EuclideanPlane P]

end criteria

end EuclidGeom
