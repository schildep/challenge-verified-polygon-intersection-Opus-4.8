import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.Independence
import Polygons2.Interior
import Polygons2.Clip
import Polygons2.CycleDecomp
import Polygons2.GoodRay

/-!
# C6 support: structural lemmas for the assembly of `exists_intersection_polys`.

`polys = cycle_decomp Mcore` (the honest clipped intersection-boundary cycles — no input
doubling).  Correctness is transferred from a clean off-boundary anchor via `even_odd_constancy`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- For a polygon with ≥2 vertices, `segments.map (·.p1)` is the vertex list. -/
lemma segments_fst_eq_vertices {poly : Polygon} (h : 2 ≤ poly.vertices.length) :
    poly.segments.map (fun s => s.p1) = poly.vertices := by
  rcases hv : poly.vertices with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · rw [hv] at h; simp at h
  · rw [hv] at h; simp at h
  · rw [segs_cons2 hv, List.map_map]
    rw [show ((fun s : LineSegment => s.p1) ∘ fun p : Vector2D × Vector2D =>
          (⟨p.1, p.2⟩ : LineSegment)) = Prod.fst from rfl]
    rw [List.map_fst_zip (by simp)]

/-- Every vertex of a polygon with ≥2 vertices lies on its boundary. -/
lemma vertex_on_boundary {poly : Polygon} (h : 2 ≤ poly.vertices.length)
    {v : Vector2D} (hv : v ∈ poly.vertices) : v ∈ poly.toBoundarySet := by
  rw [← segments_fst_eq_vertices h, List.mem_map] at hv
  obtain ⟨s, hs, hsp⟩ := hv
  refine ⟨s, hs, ?_⟩
  rw [← hsp]
  exact ⟨0, le_refl _, zero_le_one, by simp, by simp⟩

end Polygons2
end
