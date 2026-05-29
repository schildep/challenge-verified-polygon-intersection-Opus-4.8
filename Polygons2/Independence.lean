import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Telescope

/-!
# Structural lemmas about `Polygon.segments`, toward ray-independence.
-/

open Classical
noncomputable section
namespace Polygons2

lemma segs_nil {poly : Polygon} (h : poly.vertices = []) : poly.segments = [] := by
  unfold Polygon.segments; rw [h]

lemma segs_single {poly : Polygon} {v : Vector2D} (h : poly.vertices = [v]) :
    poly.segments = [] := by
  unfold Polygon.segments; rw [h]

lemma segs_cons2 {poly : Polygon} {v0 v1 : Vector2D} {rest : List Vector2D}
    (h : poly.vertices = v0 :: v1 :: rest) :
    poly.segments
      = (List.zip (v0 :: v1 :: rest) ((v1 :: rest) ++ [v0])).map (fun p => ⟨p.1, p.2⟩) := by
  unfold Polygon.segments; rw [h]

/-- Endpoints of a polygon segment are vertices of the polygon. -/
lemma seg_mem_vertices {poly : Polygon} {s : LineSegment} (hs : s ∈ poly.segments) :
    s.p1 ∈ poly.vertices ∧ s.p2 ∈ poly.vertices := by
  rcases hv : poly.vertices with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · rw [segs_nil hv] at hs; simp at hs
  · rw [segs_single hv] at hs; simp at hs
  · rw [segs_cons2 hv, List.mem_map] at hs
    obtain ⟨⟨x1, x2⟩, hx, rfl⟩ := hs
    have hz := List.of_mem_zip hx
    refine ⟨hz.1, ?_⟩
    rcases List.mem_append.1 hz.2 with h | h
    · exact List.mem_cons_of_mem _ h
    · rw [List.mem_singleton.1 h]; exact List.mem_cons_self ..

/-- The number of polygon segments whose endpoints have different `h`-status is even
(cyclic telescoping). -/
lemma segments_countP_change_even (poly : Polygon) (h : Vector2D → Bool) :
    (poly.segments.countP (fun s => h s.p1 != h s.p2)) % 2 = 0 := by
  rcases hv : poly.vertices with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · rw [segs_nil hv]; simp
  · rw [segs_single hv]; simp
  · rw [segs_cons2 hv, List.countP_map]
    exact cyclic_change_even h v0 (v1 :: rest)

end Polygons2
end
