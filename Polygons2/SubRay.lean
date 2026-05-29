import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.RayIndep
import Polygons2.Interior

/-!
# Sub-ray interior characterization.

If `q` lies on ray `r` (at parameter `t_q ≥ 0`) and `r` avoids `poly`'s vertices, then
membership of `q` in `poly.interior` is decided by the crossing parity of the *sub-ray* of
`r` starting at `q` (its crossings are exactly `r`'s crossings beyond `q`).
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- The sub-ray of `r` starting at parameter `t`. -/
def subRay (r : Ray) (t : ℚ) : Ray :=
  ⟨⟨r.origin.x + t * r.direction.x, r.origin.y + t * r.direction.y⟩, r.direction,
    r.direction_nonzero⟩

@[simp] lemma subRay_direction (r : Ray) (t : ℚ) : (subRay r t).direction = r.direction := rfl
@[simp] lemma subRay_origin (r : Ray) (t : ℚ) :
    (subRay r t).origin = ⟨r.origin.x + t * r.direction.x, r.origin.y + t * r.direction.y⟩ := rfl

/-- The sub-ray's point set is contained in the ray's (for `t ≥ 0`). -/
lemma subRay_toSet_subset (r : Ray) {t : ℚ} (ht : 0 ≤ t) : (subRay r t).toSet ⊆ r.toSet := by
  rintro x ⟨s, hs0, hsx, hsy⟩
  refine ⟨t + s, by linarith, ?_, ?_⟩
  · simp only [subRay_origin, subRay_direction] at hsx; rw [hsx]; ring
  · simp only [subRay_origin, subRay_direction] at hsy; rw [hsy]; ring

/-- A ray avoiding `poly`'s vertices ⇒ its sub-ray avoids them too. -/
lemma subRay_avoidsVertices {r : Ray} {t : ℚ} (ht : 0 ≤ t) {poly : Polygon}
    (hav : rayAvoidsVertices r poly) : rayAvoidsVertices (subRay r t) poly := by
  rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxr, hxv⟩
  have : x ∈ r.toSet ∩ poly.toVertices := ⟨subRay_toSet_subset r ht hxr, hxv⟩
  rw [hav] at this
  exact this

/-- Sub-ray interior characterization. -/
lemma mem_interior_iff_subRay (poly : Polygon) (r : Ray) {t : ℚ} (ht : 0 ≤ t)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hav : rayAvoidsVertices r poly)
    (hoff : ∀ seg ∈ poly.segments, (subRay r t).origin ∉ seg.toSet) :
    (subRay r t).origin ∈ poly.interior ↔
      intersectionRayPolygonSegmentsNumber (subRay r t) poly % 2 = 1 := by
  have hav' : rayAvoidsVertices (subRay r t) poly := subRay_avoidsVertices ht hav
  have := mem_interior_iff poly (subRay r t).origin (subRay r t) rfl hav' hnd
  rw [this]
  exact and_iff_right hoff

end Polygons2
end
