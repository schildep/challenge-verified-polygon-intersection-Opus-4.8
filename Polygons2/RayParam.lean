import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.SubRay

/-!
# Ray parameter.

For a point on a ray, its scalar parameter; used to compare crossings by distance.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- The scalar parameter of a point along a ray. -/
def rayParam (r : Ray) (x : Vector2D) : ℚ :=
  if r.direction.x ≠ 0 then (x.x - r.origin.x) / r.direction.x
  else (x.y - r.origin.y) / r.direction.y

/-- A point on a ray is reconstructed from its parameter, which is nonnegative. -/
lemma rayParam_spec (r : Ray) {x : Vector2D} (hx : x ∈ r.toSet) :
    x.x = r.origin.x + rayParam r x * r.direction.x
      ∧ x.y = r.origin.y + rayParam r x * r.direction.y
      ∧ 0 ≤ rayParam r x := by
  obtain ⟨t, ht0, htx, hty⟩ := hx
  have hpar : rayParam r x = t := by
    unfold rayParam
    by_cases hdx : r.direction.x ≠ 0
    · rw [if_pos hdx, htx]; field_simp
      ring
    · rw [if_neg hdx]
      push_neg at hdx
      have hdy : r.direction.y ≠ 0 := by
        intro h; exact r.direction_nonzero (by ext <;> simp [hdx, h])
      rw [hty]; field_simp
      ring
  rw [hpar]; exact ⟨htx, hty, ht0⟩

/-- Membership in the sub-ray ⇔ parameter is at least the sub-ray start. -/
lemma mem_subRay_iff (r : Ray) (t : ℚ) (x : Vector2D) (hx : x ∈ r.toSet) :
    x ∈ (subRay r t).toSet ↔ t ≤ rayParam r x := by
  obtain ⟨hxx, hxy, hx0⟩ := rayParam_spec r hx
  constructor
  · rintro ⟨s, hs0, hsx, hsy⟩
    -- x = subRay-origin + s•dir = origin + (t+s)•dir, so rayParam = t+s ≥ t
    simp only [subRay_origin, subRay_direction] at hsx hsy
    -- determine rayParam r x via direction component
    by_cases hdx : r.direction.x ≠ 0
    · have : rayParam r x = t + s := by
        unfold rayParam; rw [if_pos hdx, hsx]; field_simp; ring
      rw [this]; linarith
    · push_neg at hdx
      have hdy : r.direction.y ≠ 0 := by
        intro h; exact r.direction_nonzero (by ext <;> simp [hdx, h])
      have : rayParam r x = t + s := by
        unfold rayParam; rw [if_neg (by simpa using hdx), hsy]; field_simp; ring
      rw [this]; linarith
  · intro hle
    refine ⟨rayParam r x - t, by linarith, ?_, ?_⟩
    · simp only [subRay_origin, subRay_direction]; rw [hxx]; ring
    · simp only [subRay_origin, subRay_direction]; rw [hxy]; ring

end Polygons2
end
