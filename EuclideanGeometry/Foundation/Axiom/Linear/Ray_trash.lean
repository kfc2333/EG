import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (seg_nd : SegND P)

-- theorem same_extn_of_source_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target ) = seg_nd.extension

/-SegND_eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source should be replaced by the following three
  midpoint → liesint seg_nd
  midpoint → dist source = dist target
  lieson ∧ dist source = dist target → midpoint

  by the way in_seg shoud be renamed by current naming system
-/

theorem vec_eq_of_eq_dir_and_eq_length_iff {pt₁ pt₂ pt₃ pt₄ : P} (h₁ : pt₂ ≠ pt₁) (h₂ : pt₄ ≠ pt₃) : ((SEG_nd pt₁ pt₂ h₁).toDir = (SEG_nd pt₄ pt₃ h₂.symm).toDir) ∧ ((SEG pt₁ pt₂).length = (SEG pt₃ pt₄).length) ↔ (VEC pt₁ pt₂ = VEC pt₄ pt₃) := by sorry

theorem vec_eq_of_eq_dir_and_eq_length_iff' {pt₁ pt₂ pt₃ pt₄ : P} (h₁ : pt₄ ≠ pt₁) (h₂ : pt₃ ≠ pt₂) : ((SEG_nd pt₁ pt₄ h₁).toDir = (SEG_nd pt₂ pt₃ h₂).toDir) ∧ ((SEG pt₁ pt₄).length = (SEG pt₂ pt₃).length) ↔ (VEC pt₁ pt₄ = VEC pt₂ pt₃) := by sorry

end EuclidGeom
