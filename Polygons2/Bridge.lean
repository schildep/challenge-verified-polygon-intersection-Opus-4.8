import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.RayIndep
import Polygons2.Interior

/-!
# Additivity bridge: `symmDiffAll` of interiors ↔ crossing parity of the combined edges.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- Parity of a sum equals parity of the count of odd summands. -/
lemma sum_parity_eq_countP_odd {α : Type*} (f : α → ℕ) (l : List α) :
    (l.map f).sum % 2 = (l.countP (fun x => decide (f x % 2 = 1))) % 2 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    by_cases h : f x % 2 = 1 <;> simp [h] <;> omega

/-- `countP` distributes over `flatten` as a sum. -/
lemma countP_flatten {α : Type*} (q : α → Bool) (L : List (List α)) :
    (L.flatten).countP q = (L.map (fun s => s.countP q)).sum := by
  induction L with
  | nil => simp
  | cons s t ih =>
    rw [List.flatten_cons, List.countP_append, List.map_cons, List.sum_cons, ih]

/-- The bridge: for `p` off all the polygons' edges and a common vertex-avoiding ray `r`,
membership in the symmetric difference of the interiors is the crossing parity of the
concatenated edge list. -/
lemma symmDiffAll_interior_iff (polys : List Polygon) (p : Vector2D) (r : Ray)
    (hro : r.origin = p)
    (hoff : ∀ Q ∈ polys, ∀ seg ∈ Q.segments, p ∉ seg.toSet)
    (hnd : ∀ Q ∈ polys, ∀ seg ∈ Q.segments, seg.p1 ≠ seg.p2)
    (hav : ∀ Q ∈ polys, rayAvoidsVertices r Q) :
    (p ∈ symmDiffAll (polys.map Polygon.interior)) ↔
      ((polys.map (fun Q => Q.segments)).flatten.countP
        (fun seg => decide (rayIntersectsSegment r seg))) % 2 = 1 := by
  rw [mem_symmDiffAll, List.countP_map]
  have hcong : List.countP ((fun s => decide (p ∈ s)) ∘ Polygon.interior) polys
             = polys.countP (fun Q => decide (intersectionRayPolygonSegmentsNumber r Q % 2 = 1)) := by
    apply List.countP_congr
    intro Q hQ
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact (mem_interior_iff Q p r hro (hav Q hQ) (hnd Q hQ)).trans
      (and_iff_right (hoff Q hQ))
  rw [hcong]
  have hsum : (polys.map (fun Q => Q.segments)).flatten.countP
        (fun seg => decide (rayIntersectsSegment r seg)) % 2
      = polys.countP (fun Q => decide (intersectionRayPolygonSegmentsNumber r Q % 2 = 1)) % 2 := by
    rw [countP_flatten, List.map_map]
    rw [show ((fun s => List.countP (fun seg => decide (rayIntersectsSegment r seg)) s)
            ∘ fun Q => Q.segments)
          = (fun Q => intersectionRayPolygonSegmentsNumber r Q) from rfl]
    rw [← sum_parity_eq_countP_odd]
  rw [hsum]

end Polygons2
end
