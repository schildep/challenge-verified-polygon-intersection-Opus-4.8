import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.CycleDecomp
import Polygons2.ClipM
import Polygons2.ClipProps
import Polygons2.EvenDegA
import Polygons2.AcapBA
import Polygons2.CornerC
import Polygons2.Assemble2
import Polygons2.Assemble3

/-!
# The geometric construction interface.

Existence of the intersection polygon list with the properties needed by the
assembly: its boundary lies inside `∂poly1 ∪ ∂poly2`, and for points off that
boundary, the crossing parity of the combined edge list (via some vertex-avoiding
ray) decides membership in `poly1.interior ∩ poly2.interior`.

This wires together the clipping (`Mlist`), cycle realization (`cycle_decomp`),
even–odd correctness (`even_odd_constancy`/`AcapB_const`) and the assembly core.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- The intersection polygon(s) exist with the required combinatorial/parity spec. -/
lemma exists_intersection_polys (poly1 poly2 : Polygon)
    (h1_len : poly1.vertices.length ≥ 2) (h2_len : poly2.vertices.length ≥ 2)
    (h1_nondeg : ∀ seg ∈ poly1.segments, seg.p1 ≠ seg.p2)
    (h2_nondeg : ∀ seg ∈ poly2.segments, seg.p1 ≠ seg.p2)
    (h_fin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet)) :
    ∃ polys : List Polygon,
      (∀ Q ∈ polys, ∀ seg ∈ Q.segments, seg.p1 ≠ seg.p2) ∧
      (∀ p : Vector2D, (∃ Q ∈ polys, p ∈ Q.toBoundarySet) →
          p ∈ poly1.toBoundarySet ∨ p ∈ poly2.toBoundarySet) ∧
      (∀ p : Vector2D, (∀ Q ∈ polys, ∀ seg ∈ Q.segments, p ∉ seg.toSet) →
          ∃ r : Ray, r.origin = p ∧ (∀ Q ∈ polys, rayAvoidsVertices r Q) ∧
            (((polys.map (fun Q => Q.segments)).flatten.countP
                (fun seg => decide (rayIntersectsSegment r seg))) % 2 = 1 ↔
              p ∈ poly1.interior ∩ poly2.interior)) := by
  have h1e : poly1.segments ≠ [] := (segments_ne_nil_iff poly1).mpr h1_len
  have h2e : poly2.segments ≠ [] := (segments_ne_nil_iff poly2).mpr h2_len
  obtain ⟨polys, h_nd, h_cross, h_segc, _h_vertc, h_cover⟩ :=
    cycle_decomp (Mlist poly1 poly2) (Mlist_nondeg poly1 poly2)
      (Mlist_even_degree poly1 poly2 h1_nondeg h2_nondeg h1e h2e h_fin)
  exact intersection_polys_core poly1 poly2 (Mlist poly1 poly2) polys
    h1_nondeg h2_nondeg h1e h2e h_fin
    (Mlist_subset_boundary poly1 poly2)
    (fun r hav1 hav2 hS =>
      Mlist_countP_eq_insideCrossings poly1 poly2 r h1_nondeg h2_nondeg h1e h2e hav1 hav2 hS h_fin)
    (fun p hpA hpB => Mlist_mem_of_inside poly1 poly2 h1_nondeg h2_nondeg h1e h2e h_fin hpA hpB)
    (fun p hpB hpA => Mlist_mem_of_inside' poly1 poly2 h1_nondeg h2_nondeg h1e h2e h_fin hpB hpA)
    (fun {a b} hpq => AcapB_const poly1 poly2 h1_nondeg h2_nondeg h1e h2e h_fin hpq)
    h_nd h_cross h_segc h_cover

end Polygons2
end
