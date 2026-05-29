import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom

/-!
# Shared clipping interface: crossing point and inside-crossing count.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- A point where a ray meets a segment (junk value `r.origin` if they don't meet). -/
def crossingPoint (r : Ray) (seg : LineSegment) : Vector2D :=
  if h : (r.toSet ∩ seg.toSet).Nonempty then h.choose else r.origin

lemma crossingPoint_mem {r : Ray} {seg : LineSegment} (h : rayIntersectsSegment r seg) :
    crossingPoint r seg ∈ r.toSet ∧ crossingPoint r seg ∈ seg.toSet := by
  have hne : (r.toSet ∩ seg.toSet).Nonempty := h
  unfold crossingPoint
  rw [dif_pos hne]
  exact hne.choose_spec

/-- The number of poly1/poly2 edges that a ray crosses at a point inside the *other* polygon.
This is exactly the crossing count of the clipped intersection boundary `M`. -/
def insideCrossings (r : Ray) (poly1 poly2 : Polygon) : ℕ :=
  (poly1.segments.countP
      (fun e => decide (rayIntersectsSegment r e ∧ crossingPoint r e ∈ poly2.interior)))
  + (poly2.segments.countP
      (fun f => decide (rayIntersectsSegment r f ∧ crossingPoint r f ∈ poly1.interior)))

end Polygons2
end
