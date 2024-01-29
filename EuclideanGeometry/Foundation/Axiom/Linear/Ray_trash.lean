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

theorem vec_eq_of_eq_dir_and_eq_length_iff {A B C D : P} (h1 : B ≠ A) (h2 : D ≠ C) : ((SEG_nd A B h1).toDir = (SEG_nd C D h2).toDir) ∧ ((SEG A B).length = (SEG C D).length) ↔ VEC A B = VEC D C := by sorry

end EuclidGeom
