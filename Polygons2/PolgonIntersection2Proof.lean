import Polygons2.PolgonIntersection2Defs
import Polygons2.Interior
import Polygons2.Bridge
import Polygons2.Construction

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
  obtain ⟨polys, hnd, hBd, hkey⟩ :=
    exists_intersection_polys poly1 poly2 h1_len h2_len h1_nondeg h2_nondeg h_fin
  refine ⟨polys, ?_⟩
  ext p
  simp only [Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · -- p ∈ poly1.interior ∩ poly2.interior
    intro hp
    -- p avoids all boundaries of all `polys` (else it'd be on ∂poly1 or ∂poly2)
    have hpoff : ∀ Q ∈ polys, ∀ seg ∈ Q.segments, p ∉ seg.toSet := by
      intro Q hQ seg hseg hmem
      rcases hBd p ⟨Q, hQ, seg, hseg, hmem⟩ with h1 | h2
      · exact boundary_not_interior h1 hp.1
      · exact boundary_not_interior h2 hp.2
    obtain ⟨r, hro, hav, hiff⟩ := hkey p hpoff
    refine ⟨?_, ?_⟩
    · rw [symmDiffAll_interior_iff polys p r hro hpoff hnd hav]
      exact hiff.mpr hp
    · rintro ⟨Q, hQ, hQbd⟩
      rcases hBd p ⟨Q, hQ, hQbd⟩ with h1 | h2
      · exact boundary_not_interior h1 hp.1
      · exact boundary_not_interior h2 hp.2
  · -- p ∈ symmDiffAll ∧ p ∉ boundaries
    rintro ⟨hsd, hnbd⟩
    have hpoff : ∀ Q ∈ polys, ∀ seg ∈ Q.segments, p ∉ seg.toSet := by
      intro Q hQ seg hseg hmem
      exact hnbd ⟨Q, hQ, seg, hseg, hmem⟩
    obtain ⟨r, hro, hav, hiff⟩ := hkey p hpoff
    rw [symmDiffAll_interior_iff polys p r hro hpoff hnd hav] at hsd
    exact hiff.mp hsd

end Polygons2

end
