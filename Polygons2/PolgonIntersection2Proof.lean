import Polygons2.PolgonIntersection2Defs

/-!
# Polygon Intersection: Proof
-/

open Classical Set

noncomputable section

namespace Polygons2

theorem exists_polygons_inter_interior_eq_symmDiffAll_interiors_sdiff_boundaries_proof
    (poly1 poly2 : Polygon)
    (h1_len : poly1.vertices.length ≥ 2)
    (h2_len : poly2.vertices.length ≥ 2)
    (h1_nondeg : ∀ seg ∈ poly1.segments, seg.p1 ≠ seg.p2)
    (h2_nondeg : ∀ seg ∈ poly2.segments, seg.p1 ≠ seg.p2)
    (h_fin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet)) :
    ∃ polys : List Polygon,
      poly1.interior ∩ poly2.interior =
        symmDiffAll (polys.map Polygon.interior) \
          { p : Vector2D | ∃ poly ∈ polys, p ∈ poly.toBoundarySet } := by
  sorry

end Polygons2

end
