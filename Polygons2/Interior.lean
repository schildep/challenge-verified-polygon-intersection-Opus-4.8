import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.RayIndep

/-!
# Interior characterization via a single ray, and symmDiffAll membership.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- Given one vertex-avoiding ray from `p`, membership in the interior is decided by that
ray's crossing parity (using ray-independence). -/
lemma mem_interior_iff (poly : Polygon) (p : Vector2D) (r : Ray)
    (hro : r.origin = p) (hav : rayAvoidsVertices r poly)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2) :
    p ∈ poly.interior ↔
      (∀ seg ∈ poly.segments, p ∉ seg.toSet)
        ∧ intersectionRayPolygonSegmentsNumber r poly % 2 = 1 := by
  unfold Polygon.interior
  simp only [Set.mem_setOf_eq, pointAvoidsSegment]
  constructor
  · rintro ⟨hoff, hall⟩
    exact ⟨hoff, hall r hro hav⟩
  · rintro ⟨hoff, hr⟩
    refine ⟨hoff, ?_⟩
    intro r' hr'o hr'av
    rw [ray_indep poly p hoff hnd r' r hr'o hro hr'av hav]
    exact hr

/-- A point on the boundary of a polygon is not in its interior. -/
lemma boundary_not_interior {poly : Polygon} {p : Vector2D}
    (h : p ∈ poly.toBoundarySet) : p ∉ poly.interior := by
  obtain ⟨seg, hseg, hmem⟩ := h
  intro hint
  unfold Polygon.interior at hint
  simp only [Set.mem_setOf_eq, pointAvoidsSegment] at hint
  exact hint.1 seg hseg hmem

/-- Membership in a symmetric-difference-fold is the parity of the number of sets
containing the point. -/
lemma mem_symmDiffAll {V : Type*} (p : V) (l : List (Set V)) :
    p ∈ symmDiffAll l ↔ (l.countP (fun s => decide (p ∈ s))) % 2 = 1 := by
  induction l with
  | nil => simp [symmDiffAll]
  | cons s t ih =>
    have hfold : symmDiffAll (s :: t) = symmDiff s (symmDiffAll t) := rfl
    rw [hfold, Set.mem_symmDiff, List.countP_cons, ih]
    by_cases hps : p ∈ s <;> simp [hps] <;> omega

end Polygons2
end
