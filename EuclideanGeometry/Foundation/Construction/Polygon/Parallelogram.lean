import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral
import EuclideanGeometry.Foundation.Construction.Polygon.Trapezoid
import EuclideanGeometry.Foundation.Tactic.Congruence.Congruence
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

noncomputable section
namespace EuclidGeom

-- `Add class parallelogram and state every theorem in structure`

/-
There're some structural problems need further discuss.
1. In our earlier implement, we tried to claim most theorems in two different form. One of them accept arguments like (A B C D : P) ((QDR A B C D) satisfies...), the other accept arguments like (qdr : Quadrilateral) (qdr satisfies...). We called first one 'variant'. But it's seems that we can delete all 'variant's and force user to use theorems in format of (some_prg_theorem (QDR A B C D) some_conditions), in this way we can get rid of most variants.
The reason we keep the variant in our file due to problem 3. While IsPrgND is not iff with Prg_nd. Maybe some instance can solve this.
2. We have quite much criteria from Prg and/or Qdr_nd to PrgND. For user's ease, we need to provide some make methods. It's clear we should have a method like (PRG A B C D (QDR A B C D is PrgND)), It's the most intuitive make method. We should discuss the necessity of other make methods. For example, do we need a method accepts arguments qdr_cvx and (qdr_cvx satisfies IsPara)?
3. In other structures we define predicate IsXXX then define structure XXX with it's element IsXXX. Now the PrgND is not involving new predicate, so the definition of 'IsPrgND' is not related to structure PrgND naturally. How to solve this? Shall we simply provide more instances?
4. the naming of predicate currently called 'GPt_PRG_nd' and 'IsParaPara_PRG_nd', and the naming of 'IsParaPara' and 'GPt' needs discuss.
-/

/-

Recall certain definitions concerning quadrilaterals:

A QDR consists of four points; it is the generalized quadrilateral formed by these four points.

A QDR_nd is QDR that the points that adjacent is not same, namely point₂ ≠ point₁, point₃ ≠ point₂, point₄ ≠ point₃, and point₁ ≠ point₁.

We take notice that, by the well-known fact that non-trivial parallelograms are indeed convex, and considering the fine qualities of convex quadrilaterals, we decide to define parallelogram_nds as a parallelogram that is convex, while the class of parallelograms permit degenerate cases. In this way, the structure of parallelogram_nd becomes natural in both aspects of quadrilaterals and parallelograms. We do take notice that there are more straightforward ways to descibe parallelograms, such as IsPara and InGPos mentioned later. So it is due to user-friendliness that we leave quite a number of shortcuts to ease theorem-proving.

In this section we define two types of parallelograms. 'parallel_nd' deals with those quadrilaterals we commomly call parallelogram (convex), and 'parallel' with more general cases (we permite degenerate cases).

-/

-- /-- A QuadrilateralND satisfies IsPara if two sets of opposite sides are parallel respectively. -/
-- @[pp_dot]
-- def QuadrilateralND.IsParaPara {P : Type _} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := ( qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) ∧ (qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃)

-- -- scoped postfix : 50 "IsParaPara" => QuadrilateralND.IsParaPara

-- /-- A quadrilateral satisfies IsPara if it is a QuadrilateralND and satisfies IsPara as a QuadrilateralND. -/
-- @[pp_dot]
-- def Quadrilateral.IsParaPara {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
--   by_cases h : qdr.IsND
--   · exact (QuadrilateralND.mk_nd h).IsParaPara
--   · exact False

/-- A quadrilateral satisfies IsPara if it is a QuadrilateralND and satisfies IsPara as a QuadrilateralND. -/
@[pp_dot]
def Quadrilateral.IsParaPara {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr.IsND
  · have qdr_nd : QuadrilateralND P := QDR_nd' h
    exact (qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) ∧ (qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃)
  · exact False

/-- A quadrilateral is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
@[pp_dot]
def Quadrilateral.IsPrg {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃

scoped postfix : 50 "IsPrg" => Quadrilateral.IsPrg

-- `shall we define this?`
-- /-- A QuadrilateralND is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
-- @[pp_dot]
-- def QuadrilateralND.IsPrg {P : Type _} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := VEC qdr_nd.point₁ qdr_nd.point₂ = VEC qdr_nd.point₄ qdr_nd.point₃

-- scoped postfix : 50 "nd_IsPrg" => QuadrilateralND.IsPrg

/-- We define parallelogram as a structure. -/
@[ext]
structure Parallelogram (P : Type _) [EuclideanPlane P] extends Quadrilateral P where
  is_parallelogram : toQuadrilateral IsPrg

/-- Make a parallelogram with 4 points on a plane, and using condition IsPrg. -/
def Parallelogram.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsPrg) : Parallelogram P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h

scoped notation "PRG" => Parallelogram.mk_pt_pt_pt_pt

/-- Make a parallelogram with a quadrilateral, and using condition IsPrg. -/
def Parallelogram.mk_isPrg {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsPrg) : Parallelogram P where
  toQuadrilateral := qdr
  is_parallelogram := h

scoped notation "PRG'" => Parallelogram.mk_isPrg

/-- Vectors point₁ point₂ and point₄ point₃ in a parallelogram are equal. -/
theorem Parallelogram.eq_vec_of_isPrg {P : Type _} [EuclideanPlane P] {prg : Parallelogram P} : VEC prg.point₁ prg.point₂ = VEC prg.point₄ prg.point₃ := prg.is_parallelogram

/-- Vectors point₁ point₄ and point₂ point₃ in a parallelogram are equal. -/
theorem Parallelogram.eq_vec_of_isPrg' {P : Type _} [EuclideanPlane P] {prg : Parallelogram P} : VEC prg.point₁ prg.point₄ = VEC prg.point₂ prg.point₃ := by rw [← vec_add_vec prg.point₁ prg.point₂ prg.point₄, ← vec_add_vec prg.point₂ prg.point₄ prg.point₃, prg.is_parallelogram, add_comm]

/-- A parallelogram which satisfies Prallelogram.InGPos satisfies IsParaPara. -/
theorem Parallelogram.parapara_of_gpos {P : Type _} [EuclideanPlane P] {prg : Parallelogram P} (InGPos : prg.InGPos): prg.IsParaPara:= by
  unfold Quadrilateral.IsParaPara
  sorry

/-- A parallelogram which satisfies Prallelogram.InGPos is convex. -/
theorem Parallelogram.cvx_of_gpos {P : Type _} [EuclideanPlane P] {prg : Parallelogram P} (InGPos : prg.InGPos): prg.IsConvex:= by sorry

/-- We define parallelogram_nd as a structure. -/
@[ext]
structure ParallelogramND (P : Type _) [EuclideanPlane P] extends Quadrilateral_cvx P, Parallelogram P

/-- A quadrilateral is parallelogram_nd if it is both convex and satisfies qualities of a parallelogram. This definition is in agreement with the structure above. -/
@[pp_dot]
def Quadrilateral.IsPrgND {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := qdr IsConvex ∧ qdr IsPrg

scoped postfix : 50 "IsPrgND" => Quadrilateral.IsPrgND

-- /-- A QuadrilateralND is parallelogram_nd if its toQuadrilateral is both convex and satisfies qualities of a parallelogram. -/
-- @[pp_dot]
-- def QuadrilateralND.IsPrgND {P : Type _} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := Quadrilateral.IsPrgND qdr_nd.toQuadrilateral

-- scoped postfix : 50 "nd_IsPrgND" => QuadrilateralND.IsPrgND

theorem QuadrilateralND.parapara_iff_para_para {P : Type _} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : (qdr_nd.IsParaPara) ↔ (qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) ∧ (qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) := by
  constructor
  unfold Quadrilateral.IsParaPara
  simp only [dite_true, qdr_nd.nd, and_imp]
  exact fun a a_1 ↦ { left := a, right := a_1 }
  unfold Quadrilateral.IsParaPara
  simp only [dite_true, qdr_nd.nd,and_imp]
  exact fun a a_1 ↦ { left := a, right := a_1 }

/-- A parallelogram_nd satisfies InGPos. -/
theorem ParallelogramND.gpos_of_prgnd {P : Type _} [EuclideanPlane P] (prg_nd : ParallelogramND P) : prg_nd.InGPos := ⟨prg_nd.not_collinear₁₂₃, prg_nd.not_collinear₂₃₄, prg_nd.not_collinear₃₄₁, prg_nd.not_collinear₄₁₂⟩

/-- A parallelogram_nd satisfies IsParaPara. -/
theorem ParallelogramND.parapara_of_prgnd {P : Type _} [EuclideanPlane P] (prg_nd : ParallelogramND P) : prg_nd.IsParaPara := by
  unfold Quadrilateral.IsParaPara
  simp only [dite_true, prg_nd.nd]
  unfold parallel
  constructor
  have h: VEC prg_nd.point₁ prg_nd.point₂ = VEC prg_nd.point₄ prg_nd.point₃ := prg_nd.is_parallelogram
  have p: (VEC_nd prg_nd.point₁ prg_nd.point₂ prg_nd.nd₁₂.out).toProj = (VEC_nd prg_nd.point₄ prg_nd.point₃ prg_nd.nd₃₄.out.symm).toProj := by

    sorry
  sorry
  sorry

def ParallelogramND.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h: (QDR A B C D) IsPrgND) : ParallelogramND P where
  toQuadrilateral := (QDR A B C D)
  nd := h.left; convex := h.left
  is_parallelogram := h.right

scoped notation "PRG_nd" => ParallelogramND.mk_pt_pt_pt_pt

def ParallelogramND.mk_isPrgND {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsPrgND) : ParallelogramND P where
  toQuadrilateral := qdr
  nd := h.left; convex := h.left
  is_parallelogram := h.right

scoped notation "PRG_nd'" => ParallelogramND.mk_isPrgND

/-
 Using the property above, we leave such a shortcut in a way people usually sense a parallelogram. A quadrilateral A B C D is parallelogram_nd if it is ND, is a parallelogram, and satisfies InGPos.
def ParallelogramND.mk_prgND_of_gpos {P : Type _} [EuclideanPlane P] {prg : Parallelogram P} (gpos: prg.InGPos): ParallelogramND P where
  toQuadrilateral := prg.toQuadrilateral
  nd := sorry
  convex := sorry
  is_parallelogram := sorry

`name maybe changed`
scoped notation "non_triv_PRG_nd" => ParallelogramND.mk_prgND_of_gpos

A quadrilateral A B C D is parallelogram_nd if it is ND, is a parallelogram, and satisfies IsParaPara.
--def ParallelogramND.mk_prgND_of_para {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsPrg) (IsPara: (QDR_nd A B C D h).IsParaPara): ParallelogramND P where
  point₁ := A; point₂ := B; point₃ := C; point₄ := D
  nd := h
  convex := sorry
  is_parallelogram := h'

`name maybe changed`
scoped notation "IsParaPara_PRG_nd" => ParallelogramND.mk_parallelogram_para

here are two theorems using first version of definition of PRG_nd, may not be useful currently.
theorem Quadrilateral.IsPrg_nd_redef {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) (h: qdr.IsND) (h': qdr IsPrg) (h': (((QuadrilateralND.mk_nd h).angle₁.value.IsPos ∧ (QuadrilateralND.mk_nd h).angle₃.value.IsPos) ∨ ((QuadrilateralND.mk_nd h).angle₁.value.IsNeg ∧ (QuadrilateralND.mk_nd h).angle₃.value.IsNeg) ∨ ((QuadrilateralND.mk_nd h).angle₂.value.IsPos ∧ (QuadrilateralND.mk_nd h).angle₄.value.IsPos) ∨ ((QuadrilateralND.mk_nd h).angle₂.value.IsNeg ∧ (QuadrilateralND.mk_nd h).angle₄.value.IsNeg))) : (QuadrilateralND.mk_nd h).IsPrgND := sorry

theorem Parallelogram.parallelogramIs_nd_redef {P : Type _} [EuclideanPlane P] (prg : Parallelogram P) (h': prg.1.IsND) (k: ((QuadrilateralND.mk_nd h').angle₁.value.IsPos ∧ (QuadrilateralND.mk_nd h').angle₃.value.IsPos) ∨ ((QuadrilateralND.mk_nd h').angle₁.value.IsNeg ∧ (QuadrilateralND.mk_nd h').angle₃.value.IsNeg) ∨ ((QuadrilateralND.mk_nd h').angle₂.value.IsPos ∧ (QuadrilateralND.mk_nd h').angle₄.value.IsPos) ∨ ((QuadrilateralND.mk_nd h').angle₂.value.IsNeg ∧ (QuadrilateralND.mk_nd h').angle₄.value.IsNeg)) : (QuadrilateralND.mk_nd h').IsPrgND := sorry
-/

section perm

variable {P : Type _} [EuclideanPlane P]
variable (qdr : Quadrilateral P)
variable (qdr_nd : QuadrilateralND P)
variable (qdr_cvx : Quadrilateral_cvx P)
variable (prg : Parallelogram P)

/-- If a quadrilateral is a parallelogram, then its perm is also a parallelogram. -/
theorem qdr_isPrg_iff_perm_isPrg : (qdr.IsPrg) ↔ ((qdr.perm).IsPrg) := by
  unfold Quadrilateral.perm
  unfold Quadrilateral.IsPrg
  simp only
  unfold Vec.mkPtPt
  rw [eq_comm]
  refine (eq_iff_eq_of_sub_eq_sub ?H)
  rw [vsub_sub_vsub_comm]

/-- If a quadrilateral is a parallelogram_nd, then its perm is also a parallelogram_nd. -/
theorem prgND_iff_perm_prgND : (qdr.IsPrgND) ↔ ((qdr.perm).IsPrgND) := by sorry

/-- If a quadrilateral satisfies IsParaPara, then its perm also satisfies IsParaPara. -/
theorem para_iff_perm_para : (qdr.IsParaPara) ↔ ((qdr.perm).IsParaPara) := by sorry

/-- If a quadrilateral_nd satisfies IsParaPara, then its perm also satisfies IsParaPara. -/
theorem qdrND_IsParaPara_iff_perm_IsParaPara : (qdr_nd.IsParaPara) ↔ ((qdr_nd.perm).IsParaPara) := by sorry

/-- If a quadrilateral satisfies IsParaPara, then its perm also satisfies IsParaPara. -/
theorem qdr_gpos_iff_perm_gpos : (qdr.InGPos) ↔ ((qdr.perm).InGPos) := by sorry

end perm

section flip

variable {P : Type _} [EuclideanPlane P]
variable (qdr : Quadrilateral P)
variable (qdr_nd : QuadrilateralND P)
variable (qdr_cvx : Quadrilateral_cvx P)
variable (prg : Parallelogram P)

/-- If a quadrilateral is a parallelogram, then its flip is also a parallelogram. -/
theorem qdr_isPrg_iff_flip_isPrg : (qdr.IsPrg) ↔ ((qdr.flip).IsPrg) := by
  unfold Quadrilateral.flip
  unfold Quadrilateral.IsPrg
  simp only
  unfold Vec.mkPtPt
  refine (eq_iff_eq_of_sub_eq_sub ?H)
  sorry

/-- If a quadrilateral is a parallelogram_nd, then its flip is also a parallelogram_nd. -/
theorem qdr_isPrgND_iff_qdr_isPrgND : (qdr.IsPrgND) ↔ ((qdr.flip).IsPrgND) := by
  sorry

/-- If a quadrilateral satisfies IsParaPara, then its flip also satisfies IsParaPara. -/
theorem qdr_IsParaPara_iff_flip_IsParaPara : (qdr.IsParaPara) ↔ ((qdr.flip).IsParaPara) := by sorry

/-- If a quadrilateral_nd satisfies IsParaPara, then its flip also satisfies IsParaPara. -/
theorem qdrND_IsParaPara_iff_flip_IsParaPara : (qdr_nd.IsParaPara) ↔ ((qdr_nd.flip).IsParaPara) := by sorry

/-- If a quadrilateral satisfies IsParaPara, then its flip also satisfies IsParaPara. -/
theorem qdr_gpos_iff_flip_gpos : (qdr.InGPos) ↔ ((qdr.flip).InGPos) := by sorry

end flip

section criteria_prgND_of_prg

variable {P : Type _} [EuclideanPlane P]
variable (qdr_nd : QuadrilateralND P)
variable (prg : Parallelogram P)

/-- If the 2nd, 3rd and 4th points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₁ (h : ¬ collinear prg.point₂ prg.point₃ prg.point₄) : prg.IsPrgND := by
  sorry

/-- If the 3rd, 4th and 1st points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₂ (h: ¬ collinear prg.point₃ prg.point₄ prg.point₁) : prg.IsPrgND := by
  sorry

/-- If the 4th, 1st and 2nd points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₃ (h: ¬ collinear prg.point₄ prg.point₁ prg.point₂) : prg.IsPrgND := by
  sorry

/-- If the 1st, 2nd and 3rd points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₄ (h: ¬ collinear prg.point₁ prg.point₂ prg.point₃) : prg.IsPrgND := by
  sorry

/- We leave these four theorems as interface for the user. They are simply replica of the theorems above. -/
theorem prg_isPrgND_iff_not_collinear₁ : prg.IsPrgND ↔ (¬ collinear prg.point₂ prg.point₃ prg.point₄) := sorry

theorem prg_isPrgND_iff_not_collinear₂ : prg.IsPrgND ↔ (¬ collinear prg.point₃ prg.point₄ prg.point₁) := sorry

theorem prg_isPrgND_iff_not_collinear₃ : prg.IsPrgND ↔ (¬ collinear prg.point₄ prg.point₁ prg.point₂) := sorry

theorem prg_isPrgND_iff_not_collinear₄ : prg.IsPrgND ↔ (¬ collinear prg.point₁ prg.point₂ prg.point₃) := sorry

end criteria_prgND_of_prg

/- `besides these, we also need the make method from qdr and qdr_nd to prg_nd `-/

-- `the form of all the codes above needs more discussion`

section criteria_prgND_of_qdrND

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P} (nd : (QDR A B C D).IsND)
variable (qdr : Quadrilateral P) (qdr_nd : QuadrilateralND P)

/-- If a QuadrilateralND satisfies IsParaPara and its 1st, 2nd and 3rd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₄ (h: qdr_nd.IsParaPara) (notcollinear : ¬ collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsPrgND := by
  sorry

/-- If a QuadrilateralND satisfies IsParaPara and its 2nd, 3rd and 4th points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₁ (h: qdr_nd.IsParaPara) (notcollinear : ¬ collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsPrgND := by
  sorry

/-- If a QuadrilateralND satisfies IsParaPara and its 3rd, 4th and 1st points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₂ (h: qdr_nd.IsParaPara) (notcollinear : ¬ collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsPrgND := by
  sorry

/-- If a QuadrilateralND satisfies IsParaPara and its 4th, 1st and 2nd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₃ (h: qdr_nd.IsParaPara) (notcollinear : ¬ collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsPrgND := sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 1st, 2nd and 3rd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₄ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsPrgND := by
  sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 2nd, 3rd and 4th points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₁ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsPrgND := by sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 3rd, 4th and 1st points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₂ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsPrgND := by sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 4th, 1st and 2nd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₃ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsPrgND := by sorry

/-- If edge_nd₁₂, edge_nd₃₄ and edge_nd₁₄, edge_nd₂₃ of a QuadrilateralND are equal in value respectively, and angle₁ and angle₃ are of the same sign, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_length_eq_length_eq_angle_sign (h₁ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (h₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length) (h : (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₃.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg)) : qdr_nd.IsPrgND := by sorry

/-- If edge_nd₁₂, edge_nd₃₄ and edge_nd₁₄, edge_nd₂₃ of a QuadrilateralND are equal in value respectively, and angle₂ and angle₄ are of the same sign, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_length_eq_length_eq_angle_sign' (h₁ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (h₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length) (h : (qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)) : qdr_nd.IsPrgND := by sorry

end criteria_prgND_of_qdrND

section criteria_prg_of_qdrND

variable {P : Type _} [EuclideanPlane P]
variable {A B C D: P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr_nd : QuadrilateralND P)
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

-- `why this theorem used two set of parallel and equal?`
/-- If edge_nd₁₂ and edge_nd₃₄ of a QuadrilateralND are equal in value and parallel, and so do edge_nd₁₄ and edge_nd₂₃, then it is a parallelogram. -/
theorem qdrND_is_prg_of_parapara_eq_length_eq_length (h : qdr_nd.IsParaPara) (h₂ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (H₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length): qdr_nd.IsPrg := by
  sorry

/-- If the midpoint of the two diags of a QuadrilateralND are exactly the same, then it is a parallelogram. -/
theorem qdrND_is_prg_of_diag_inx_eq_midpt_eq_midpt (h' : (qdr_nd.diag₁₃).midpoint = (qdr_nd.diag₂₄).midpoint) : qdr_nd.IsPrg := by
  sorry

/-- If the midpoint of AC and BD are exactly the same, then QuadrilateralND A B C D is a parallelogram. -/
theorem qdrND_is_prg_of_diag_inx_eq_midpt_eq_midpt_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (QuadrilateralND.mk_nd nd).IsPrg := by
  sorry

end criteria_prg_of_qdrND

section criteria_prgND_of_qdrcvx

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable (qdr_cvx : Quadrilateral_cvx P)
variable (qdr : Quadrilateral P)

/-- If edge_nd₁₂ and edge_nd₃₄ of a quadrilateral_cvx are parallel, and so do edge_nd₁₄ and edge_nd₂₃, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_iff_parapara : qdr_cvx.IsParaPara ↔ qdr_cvx.IsPrgND := by
  constructor
  sorry
  sorry

/-- If edge_nd₁₂ and edge_nd₃₄ of a quadrilateral_cvx are equal in length, and so do edge_nd₁₄ and edge_nd₂₃, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_eq_length_eq_length (h₁ : qdr_cvx.edge_nd₁₂.length = qdr_cvx.edge_nd₃₄.length) (h₂ : qdr_cvx.edge_nd₁₄.length = qdr_cvx.edge_nd₂₃.length) : qdr_cvx.IsPrgND := by
  -- We would like to transfer the goal from proving two vectors being equal to proving ParaPara.
  apply (qdrcvx_is_prgND_iff_parapara qdr_cvx).mp
  unfold Quadrilateral.IsParaPara
  -- Simpify the goal by the non-degenerate condition.
  simp only [dite_true, qdr_cvx.nd]
  -- We would like to prove the parallel relationship by the equation of angles. Therefore it is necessary to prove (by SSS) triangle_nd₁ and triangle_nd₃ being congruent.
  -- Lemma₁: edge₂ of the triangles being equal in length.
  have eq_edge₂: qdr_cvx.triangle_nd₁.edge₂.length = qdr_cvx.triangle_nd₃.edge₂.length := by
    rw [length_of_rev_eq_length']
    rfl
  -- Lemma₂: edge₃ of the triangles being equal in length.
  have eq_edge₃: qdr_cvx.triangle_nd₁.edge₃.length = qdr_cvx.triangle_nd₃.edge₃.length := by
    rw [length_of_rev_eq_length']
    exact h₂
  -- The third set of length equation comes from initial conditions. We would also use the cclock condition of convex quadrilaterals because we need equation of angles.
  have tri_congr : qdr_cvx.triangle_nd₁ IsCongrTo qdr_cvx.triangle_nd₃ := TriangleND.congr_of_SSS_of_eq_orientation h₁ eq_edge₂ eq_edge₃ qdr_cvx.cclock_eq
  -- The trivial conclusion that rays point₂ point₄ and point₄ point₂ are reverse in direction. We need this to prove two sets of sides in qdr_cvx being parallel.
  have rev_todir: qdr_cvx.diag_nd₂₄.toRay.toDir = - qdr_cvx.diag_nd₂₄.reverse.toRay.toDir := by simp only [SegND.toRay_toDir_eq_toDir, Dir.quotient_mk_eq, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir, neg_neg]
  -- Prove that two angle end_rays (actually torays of one set of sides in qdr_cvx) being reverse in direction (equal in toProj, namely parallel) using the theorem concerning equal values and reverse directions in dir₂.
  have rev_todir₁: qdr_cvx.triangle_nd₁.angle₁.dir₂ = - qdr_cvx.triangle_nd₃.angle₁.dir₂ := neg_eq_iff_eq_neg.mp (id rev_todir.symm)
  -- Prove that two angle end_rays (actually torays of one set of sides in qdr_cvx) being reverse in direction (equal in toProj, namely parallel) using the theorem concerning equal values and reverse directions in dir₁.
  have rev_todir₂: qdr_cvx.triangle_nd₁.angle₃.dir₁ = - qdr_cvx.triangle_nd₃.angle₃.dir₁ := rev_todir
  -- We complete the transferring from toDir to toProj in this step. This is due to being parallel is namely equal in toProj.
  have eq_toproj₁: qdr_cvx.triangle_nd₁.angle₁.start_ray.toProj = qdr_cvx.triangle_nd₃.angle₁.start_ray.toProj := by
    -- Using this theorem we are able to relate toDir to toProj in a ray. Note that we need to choose one of the subgoals.
    apply Dir.toProj_eq_toProj_iff.mpr
    -- Choose the subgoal concerning reverse directions.
    right
    -- Using this theorem we are able to relate the equation of angles to the relationship of toProjs, considering the known relationship of rays point₂ point₄ and point₄ point₂.
    apply Angle.dir₁_eq_neg_dir₁_of_value_eq_of_dir₂_eq_neg_dir₂ rev_todir₁ tri_congr.angle₁
  -- We hope to finish the transferring from rays to segments.
  have ray_to_seg_toproj₁: qdr_cvx.triangle_nd₁.angle₁.start_ray.toProj = qdr_cvx.edge_nd₁₄.reverse.toProj := by rfl
  -- In this way we transfer a segment to its reverse in terms of toProjs to satisfy the need of edges in qdr_cvx.
  have rev_toproj_eq_toproj₁: qdr_cvx.edge_nd₁₄.reverse.toProj = qdr_cvx.edge_nd₁₄.toProj := by simp only [VecND.toDir_toProj, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toProj]
  rw [rev_toproj_eq_toproj₁] at ray_to_seg_toproj₁
  -- We hope to finish the transferring from rays to segments.
  have ray_to_seg_toproj₂: qdr_cvx.triangle_nd₃.angle₁.start_ray.toProj = qdr_cvx.edge_nd₂₃.toProj := by rfl
  -- We transfer lemma eq_toproj₁ to the target relationship.
  rw [ray_to_seg_toproj₁, ray_to_seg_toproj₂] at eq_toproj₁
  -- We complete the transferring from toDir to toProj in this step. This is due to being parallel is namely equal in toProj.
  have eq_toproj₂: qdr_cvx.triangle_nd₁.angle₃.end_ray.toProj = qdr_cvx.triangle_nd₃.angle₃.end_ray.toProj := by
    -- Using this theorem we are able to relate toDir to toProj in a ray. Note that we need to choose one of the subgoals.
    apply Dir.toProj_eq_toProj_iff.mpr
    -- Choose the subgoal concerning reverse directions.
    right
    -- Using this theorem we are able to relate the equation of angles to the relationship of toProjs, considering the known relationship of rays point₂ point₄ and point₄ point₂.
    apply Angle.dir₂_eq_neg_dir₂_of_value_eq_of_dir₁_eq_neg_dir₁ rev_todir₂ tri_congr.angle₃
  -- We hope to finish the transferring from rays to segments.
  have ray_to_seg_toproj₃: qdr_cvx.triangle_nd₁.angle₃.end_ray.toProj = qdr_cvx.edge_nd₁₂.reverse.toProj := by rfl
  -- In this way we transfer a segment to its reverse in terms of toProjs to satisfy the need of edges in qdr_cvx.
  have rev_toproj_eq_toproj₃: qdr_cvx.edge_nd₁₂.reverse.toProj = qdr_cvx.edge_nd₁₂.toProj := by simp only [VecND.toDir_toProj, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toProj]
  rw [rev_toproj_eq_toproj₃] at ray_to_seg_toproj₃
  -- We hope to finish the transferring from rays to segments.
  have ray_to_seg_toproj₄: qdr_cvx.triangle_nd₃.angle₃.end_ray.toProj = qdr_cvx.edge_nd₃₄.reverse.toProj := by rfl
  -- In this way we transfer a segment to its reverse in terms of toProjs to satisfy the need of edges in qdr_cvx.
  have rev_toproj_eq_toproj₄: qdr_cvx.edge_nd₃₄.reverse.toProj = qdr_cvx.edge_nd₃₄.toProj := by simp only [VecND.toDir_toProj, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toProj]
  rw [rev_toproj_eq_toproj₄] at ray_to_seg_toproj₄
  -- We transfer lemma eq_toproj₂ to the target relationship.
  rw [ray_to_seg_toproj₃, ray_to_seg_toproj₄] at eq_toproj₂
  -- The goal is closed by eq_toproj₁ and eq_toproj₂.
  exact ⟨eq_toproj₂, eq_toproj₁⟩
  -- Done!

/-- If edge_nd₁₂ and edge_nd₃₄ of a quadrilateral_cvx are not only equal in length but also parallel, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_para_eq_length (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₂.length = qdr_cvx.edge_nd₃₄.length) : qdr_cvx.IsPrgND := by
  -- We would like to transfer the goal from proving two vectors being equal to proving ParaPara.
  apply (qdrcvx_is_prgND_iff_parapara qdr_cvx).mp
  unfold Quadrilateral.IsParaPara
  -- Simpify the goal by the non-degenerate condition.
  simp only [dite_true, qdr_cvx.nd]
  -- As the condition is given in the form of segments being parallel (namely toProjs being equal), there remains two possibilities: toDirs of these segments being equal or reverse. As we will point out later, one of the conditions will lead to the impossible conclusion that two diagonals in qdr_cvx being parallel, thus is a contradiction. In the remaining case, we can finally conclude that qdr_cvx is indeed a parallelogram_nd.
  have h: qdr_cvx.edge_nd₁₂.toDir = qdr_cvx.edge_nd₃₄.toDir ∨ qdr_cvx.edge_nd₁₂.toDir = - qdr_cvx.edge_nd₃₄.toDir := by apply Dir.toProj_eq_toProj_iff.mp h₁
  rcases h with case_not_convex | case_convex
  -- In the case in which the quadrilateral is not convex, our goal is to prove that two diagonals in qdr_cvx are parallel, thus we can produce a contradiction.
  -- We would like to use SAS to prove triangle₁ and triangle₄ of the 'convex' quadrilateral being congruent.
  have angle₁_eq_angle₄: (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁).value = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄).value := by
    -- By using this theorem we devide the equation of values of angles into two subgoals of reverse directions.
    apply Angle.value_eq_of_dir_eq_neg_dir
    -- The first is to prove the directions of the start rays of the two angles are in reverse.
    -- In the following comments, we denote A for point₁, B for point₂, C for point₃ and D for point₄ for convenience.
    -- Lemma: the direction of the start ray of ∠ C D A, namely ray D C, is the opposite of that of segment C D.
    have ray₄₃_todir_eq_seg_nd₃₄_rev_todir: qdr_cvx.edge_nd₃₄.reverse.toDir = (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁).start_ray.toDir := by rfl
    -- Lemma: the direction of the start ray of ∠ B A D, namely ray A B, is the same as that of segment A B.
    have ray₁₂_toDir_eq_Seg_nd₁₂_toDir: qdr_cvx.edge_nd₁₂.toDir = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄).start_ray.toDir := by rfl
    -- We state the fact that segment C D and D C has an opposite pair of directions.
    have seg_nd₄₃_toDir_neg_seg_nd₃₄_rev_toDir: qdr_cvx.edge_nd₃₄.reverse.toDir = - qdr_cvx.edge_nd₃₄.toDir := by simp only [Dir.quotient_mk_eq, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir]
    -- In this way we transfer the discussion from segments to rays via the lemmas above and the condition of qdr_cvx being non-convex is used to transfer from C D to A B.
    rw [case_not_convex.symm, ray₄₃_todir_eq_seg_nd₃₄_rev_todir, ray₁₂_toDir_eq_Seg_nd₁₂_toDir] at seg_nd₄₃_toDir_neg_seg_nd₃₄_rev_toDir
    exact seg_nd₄₃_toDir_neg_seg_nd₃₄_rev_toDir
    -- The second is to prove the directions of the end rays of the two angles, namely A D and D A, are in reverse.
    have rev_dir_of_rev_seg: qdr_cvx.edge_nd₁₄.reverse.toRay.toDir = - qdr_cvx.edge_nd₁₄.toRay.toDir := by simp only [SegND.toRay_toDir_eq_toDir, Dir.quotient_mk_eq, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir]
    exact rev_dir_of_rev_seg
  -- The first pair of edge equations: A D = D A in length.
  have edge₂_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).1.edge₂.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).1.edge₂.length := by apply length_of_rev_eq_length'
  -- The second pair of edge equations: D C = A B in length.
  have edge₃_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).1.edge₃.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).1.edge₃.length := by
    -- We need to adjust D C to C D to suit the condition h₂.
    have eq_length: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).1.edge₃.length = qdr_cvx.edge_nd₃₄.length := by apply length_of_rev_eq_length'
    rw [eq_length]
    exact h₂.symm
  -- With the 3 lemmas above, we can conclude that these two triangles are congruent. NOw we would like to use the property of congruence to prove certain relationships of angles.
  have tri_congr₁: TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁ IsCongrTo TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄ := by apply TriangleND.congr_of_SAS edge₂_eq angle₁_eq_angle₄ edge₃_eq
  -- The trird angles of the triangles are equal in value.
  have eq_angle₃: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.value = (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.value := by
    rcases tri_congr₁ with ⟨_, _, _, _, _, propf⟩
    exact propf.symm
  -- We need a few steps for the conclusion of reverse dir₁. We state that rays A D and D A has opposite directions.
  have rev_dir_of_rev_ray₁: - qdr_cvx.edge_nd₁₄.toDir = qdr_cvx.edge_nd₁₄.reverse.toDir := by simp only [Dir.quotient_mk_eq, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir]
  -- Via the lamma above we see that the reverse of one of the target rays is of the same direction as the other target ray.
  have rev_dir_eq_dir: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.reverse.toDir = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.start_ray.toDir := rev_dir_of_rev_ray₁
  -- Substitute the reverse ray.
  have rev_dir_of_rev_ray₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.toDir := by rfl
  rw [rev_dir_of_rev_ray₂] at rev_dir_eq_dir
  -- Simplify the results, we conclude that the directions of the start rays of angle₃ of the two triangles are reverse.
  have rev_dir₁: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.dir₁ = - (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.dir₁ := neg_eq_iff_eq_neg.mp rev_dir_eq_dir
  have rev_dir_of_rev_ray₃:  (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.reverse.toDir =  - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.toDir := by simp only [Ray.reverse_toDir, Angle.end_ray_toDir]
  -- Via the lamma above we see that the reverse of one of the target rays is of the same direction as the other target ray.
  have rev_todir: - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.end_ray.toDir := by
    rw [rev_dir_of_rev_ray₃]
    simp only [Angle.end_ray_toDir, neg_neg]
    apply (Angle.dir₂_eq_neg_dir₂_of_value_eq_of_dir₁_eq_neg_dir₁ rev_dir₁ eq_angle₃.symm)
  -- Via trivial properties we can simplify the result and get rid of the reverse ray, introducing the target statement.
  have rev_dir_of_rev_ray₄: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.toDir := by rfl
  rw [rev_dir_of_rev_ray₄] at rev_todir
  simp only [neg_neg] at rev_todir
  -- From the relationship of reverse directions, we can get the target relationship of equal toProjs (namely parallel).
  have eq_toproj: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.toProj = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.end_ray.toProj := by
    -- Using this theorem we are able to relate toDir to toProj in a ray. Note that we need to choose one of the subgoals.
    apply Dir.toProj_eq_toProj_iff.mpr
    -- Choose the subgoal concerning reverse directions.
    right
    exact rev_todir
  -- We hope to finish the transferring from rays to segments.
  have ray_eq_seg_toproj: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.end_ray.toProj = qdr_cvx.diag_nd₂₄.reverse.toProj := by rfl
  -- In this way we transfer a segment to its reverse in terms of toProjs to satisfy the need of edges in qdr_cvx.
  have rev_seg_eq_proj: qdr_cvx.diag_nd₂₄.reverse.toProj = qdr_cvx.diag_nd₂₄.toProj := by simp only [VecND.toDir_toProj, SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toProj]
  rw [rev_seg_eq_proj, eq_toproj.symm] at ray_eq_seg_toproj
  -- From the lemmas above we see that the two diagonals of qdr_cvx are parallel, which is not allowed in a qdr_cvx.
  have diag_ng_para: ¬ qdr_cvx.diag_nd₁₃.toProj = qdr_cvx.diag_nd₂₄.toProj := qdr_cvx.diag_not_para
  -- Thus we conclude a contradiction and close this section.
  contradiction
  -- In the following case where qdr_cvx is indeed convex, we will still use the property of edges being parallel to prove angles being equal and conduct another pair of parallel edges. We will still be in favour of using SAS to prove triangle₂ and triangle₄ of qdr_cvx being congruent.
  have rev_seg_dir_rev: qdr_cvx.diag_nd₁₃.reverse.toDir = - qdr_cvx.diag_nd₁₃.toDir := by simp only [Dir.quotient_mk_eq,
      SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir]
  have eq_angle₁: qdr_cvx.triangle_nd₂.angle₁.value = qdr_cvx.triangle_nd₄.angle₁.value := by
    -- By using this theorem we devide the equation of values of angles into two subgoals of corresponding directions.
    apply Angle.value_eq_of_dir_eq_neg_dir
    -- The first pair is trivial under the convex condition.
    exact case_convex
    -- The second pair. We will use these trivial properties. As we know the relationship of toDir of segments under this case, we decide to transfer the toDirs of rays to segments.
    have end_ray_seg_eq_dir: qdr_cvx.triangle_nd₂.angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
    have end_ray_seg_rev_dir: qdr_cvx.triangle_nd₄.angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
    -- A trivial property of the direction of segments.
    rw [end_ray_seg_eq_dir.symm, end_ray_seg_rev_dir.symm] at rev_seg_dir_rev
    -- By transferring the quantities we need into one equation, we close the goal with our target relationship.
    exact neg_eq_iff_eq_neg.mp (id rev_seg_dir_rev.symm)
  -- Proving the property of congruence, like above, we need two sets of edges being equal in length, satisfied trivially.
  have eq_edge₂: qdr_cvx.triangle_nd₂.1.edge₂.length = qdr_cvx.triangle_nd₄.1.edge₂.length := length_of_rev_eq_length'
  have eq_edge₃: qdr_cvx.triangle_nd₂.1.edge₃.length = qdr_cvx.triangle_nd₄.1.edge₃.length := h₂
  -- We now have the property of congruence.
  have tri_congr₂: qdr_cvx.triangle_nd₂ IsCongrTo qdr_cvx.triangle_nd₄ := TriangleND.congr_of_SAS eq_edge₂ eq_angle₁ eq_edge₃
  -- We can now use this property to prove angles being equal. This pair of equal angles comes straight from tri_congr₂.
  have eq_angle₃: qdr_cvx.triangle_nd₂.angle₃.value = qdr_cvx.triangle_nd₄.angle₃.value := tri_congr₂.angle₃
  -- Angles being equal implies parallel relationships, and we hope qdr_cvx becomes a parallelogram.
  have rev_todir₁: qdr_cvx.triangle_nd₂.angle₃.dir₁ = qdr_cvx.triangle_nd₄.angle₃.start_ray.reverse.toDir := by
    -- By using the same technique we can cover this proof.
    have start_ray_seg_rev_dir: qdr_cvx.triangle_nd₂.angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
    have start_ray_seg_eq_dir: qdr_cvx.triangle_nd₄.angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
    rw [start_ray_seg_rev_dir.symm, start_ray_seg_eq_dir.symm] at rev_seg_dir_rev
    -- By transferring the quantities we need into one equation, we close the goal with our target relationship.
    exact rev_seg_dir_rev
    -- In this way we transfer a ray to its reverse in terms of toDirs to satisfy the need of the proof.
  -- Again we get rid of the reverse ray to get the target.
  have rev_dir_of_rev_ray₅: qdr_cvx.triangle_nd₄.angle₃.start_ray.reverse.toDir = - qdr_cvx.triangle_nd₄.angle₃.dir₁ := by simp only [Ray.reverse_toDir, Angle.start_ray_toDir]
  rw [rev_dir_of_rev_ray₅] at rev_todir₁
  -- By using theorems concerning angles of equal value and reverse directions of start rays, we get the target relationship of reverse directions of end rays.
  have rev_dir₂: qdr_cvx.triangle_nd₂.angle₃.dir₂ = - qdr_cvx.triangle_nd₄.angle₃.dir₂ := by apply (Angle.dir₂_eq_neg_dir₂_of_value_eq_of_dir₁_eq_neg_dir₁ rev_todir₁ eq_angle₃)
  -- Once again we make the transfer from rays to segments.
  have seg_rev_ray_todir: qdr_cvx.triangle_nd₂.angle₃.dir₂ = qdr_cvx.edge_nd₂₃.reverse.toDir := by rfl
  have seg_eq_ray_todir: qdr_cvx.triangle_nd₄.angle₃.dir₂ = qdr_cvx.edge_nd₁₄.toDir := by rfl
  have rev_todir_of_rev_seg: qdr_cvx.edge_nd₂₃.reverse.toDir = - qdr_cvx.edge_nd₂₃.toDir := by simp only [Dir.quotient_mk_eq,
    SegND.toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir]
  rw [seg_rev_ray_todir, seg_eq_ray_todir, rev_todir_of_rev_seg] at rev_dir₂
  simp only [neg_inj] at rev_dir₂
  -- Now we have the target toProj equation, namely parallel relationship of the wanted edges.
  have qdrcvx_para: qdr_cvx.edge_nd₂₃.toProj = qdr_cvx.edge_nd₁₄.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    left
    exact rev_dir₂
  -- With one set of parallel edges, we can close the goal.
  exact ⟨h₁,qdrcvx_para.symm⟩
  -- Done!

/-- If edge_nd₁₄ and edge_nd₂₃ of a quadrilateral_cvx are not only equal in length but also parallel, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_para_eq_length' (h₁ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) (h₂ : qdr_cvx.edge_nd₁₄.length = qdr_cvx.edge_nd₂₃.length) : qdr_cvx.IsPrgND := by sorry

/-- If angle₁ and angle₃ of a quadrilateral_cvx are equal in value, and so do angle₂ and angle₄, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_eq_angle_value_eq_angle_value (h₁ : qdr_cvx.angle₁.value = qdr_cvx.angle₃.value) (h₂ : qdr_cvx.angle₂.value = qdr_cvx.angle₄.value) : qdr_cvx.IsPrgND := by sorry

/-- If the midpoint of the two diags of a quadrilateral_cvx are exactly the same, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_diag_eq_midpt (h' : qdr_cvx.diag_nd₁₃.midpoint = qdr_cvx.diag_nd₂₄.midpoint) : qdr_cvx.IsPrgND := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_diag_eq_midpt_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (QDR_cvx' cvx).IsPrgND := by
  sorry

end criteria_prgND_of_qdrcvx

section property

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type _} [EuclideanPlane P] (prg : Parallelogram P)

/-- The lengths of segments point₁ point₂ and point₃ point₄ in a parallelogram are equal. -/
theorem eq_length_of_isPrg : (prg.edge₁₂).length = (prg.edge₃₄).length := by sorry

theorem eq_length_of_isPrg_variant (h : (QDR A B C D).IsPrg) : (SEG A B).length = (SEG C D).length := by sorry

/-- The lengths of segments point₁ point₄ and point₂ point₃ in a parallelogram are equal. -/
theorem eq_length_of_isPrg' : (prg.edge₁₄).length = (prg.edge₂₃).length := by sorry

theorem eq_length_of_isPrg'_variant (h : (QDR A B C D).IsPrg) : (SEG A D).length = (SEG B C).length := by sorry

/-- The midpoints of segments point₁ point₃ and point₂ point₄ in a parallelogram are exactly the same. -/
theorem eq_midpt_of_diag_of_isPrg : (prg.diag₁₃).midpoint = (prg.diag₂₄).midpoint := by sorry

/-- In a parallelogram the sum of the square of the sides is equal to that of the two diags. -/
theorem parallelogram_law : 2 * (prg.edge₁₂).length ^ 2 + 2 * (prg.edge₂₃).length ^ 2 = (prg.diag₁₃).length ^ 2 + (prg.diag₂₄).length ^ 2 := by sorry

/-- In a parallelogram A B C D the sum of the square of the sides is equal to that of the two diags, namely 2 * AB² + 2 * BC² = AC² + BD². -/
theorem parallelogram_law_variant (h : (QDR A B C D).IsPrg) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 := by sorry

end property

section property_nd

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type _} [EuclideanPlane P] (prg_nd : ParallelogramND P)

/-- In a parallelogram_nd, edge_nd₁₂ and edge₃₄ are parallel. -/
theorem para_of_isPrgND : prg_nd.edge_nd₁₂ ∥ prg_nd.edge_nd₃₄ := (prg_nd.parapara_iff_para_para.mp prg_nd.parapara_of_prgnd).left

/-- In a parallelogram_nd, edge_nd₁₄ and edge₂₃ are parallel. -/
theorem para_of_isPrgND' : prg_nd.edge_nd₁₄ ∥ prg_nd.edge_nd₂₃ := (prg_nd.parapara_iff_para_para.mp prg_nd.parapara_of_prgnd).right

/-- The toDirs of edge_nd₁₂ and edge_nd₃₄ of a parallelogram_nd remain reverse. -/
theorem todir_eq_of_isPrgND : prg_nd.edge_nd₁₂.toDir = - prg_nd.edge_nd₃₄.toDir := by sorry

/-- The toDirs of edge_nd₁₄ and edge_nd₂₃ of a parallelogram_nd remain the same. -/
theorem todir_eq_of_isPrgND' : prg_nd.edge_nd₁₄.toDir = prg_nd.edge_nd₂₃.toDir := by sorry

/-- In a parallelogram_nd, angle₂ and angle₄ are equal. -/
theorem eq_angle_value_of_isPrgND : prg_nd.angle₂.value = prg_nd.angle₄.value := by sorry

/-- In a parallelogram_nd, angle₁ and angle₃ are equal. -/
theorem eq_angle_value_of_isPrgND' : prg_nd.angle₁.value = prg_nd.angle₃.value := by sorry

/-- In a parallelogram_nd the intersection of the two diags is the same as the midpoint of diag₁₃. -/
theorem eq_midpt_of_diag_inx_of_isPrgND : prg_nd.diag_inx = prg_nd.diag_nd₁₃.midpoint := by sorry

/-- In a parallelogram_nd the intersection of the two diags is the same as the midpoint of diag₂₄. -/
theorem eq_midpt_of_diag_inx_of_isPrgND' : prg_nd.diag_inx = prg_nd.diag_nd₂₄.midpoint := by sorry

end property_nd
