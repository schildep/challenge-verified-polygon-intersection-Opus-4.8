import Mathlib
import Polygons2.PolgonIntersection2Defs

/-!
# Geometry foundations for the polygon intersection proof

Algebraic helpers on `Vector2D` over `ℚ` and cross-product characterizations of
membership in `Ray.toSet` and `LineSegment.toSet`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- Vector subtraction. -/
def vsub (p q : Vector2D) : Vector2D := ⟨p.x - q.x, p.y - q.y⟩

/-- 2D cross product (scalar). -/
def cross (u v : Vector2D) : ℚ := u.x * v.y - u.y * v.x

/-- 2D dot product. -/
def dot (u v : Vector2D) : ℚ := u.x * v.x + u.y * v.y

@[simp] lemma vsub_x (p q : Vector2D) : (vsub p q).x = p.x - q.x := rfl
@[simp] lemma vsub_y (p q : Vector2D) : (vsub p q).y = p.y - q.y := rfl
@[simp] lemma cross_def (u v : Vector2D) : cross u v = u.x * v.y - u.y * v.x := rfl
@[simp] lemma dot_def (u v : Vector2D) : dot u v = u.x * v.x + u.y * v.y := rfl

lemma cross_self (u : Vector2D) : cross u u = 0 := by simp [cross]; ring

lemma dot_pos_of_ne_zero {u : Vector2D} (h : u ≠ ⟨0,0⟩) : 0 < dot u u := by
  simp only [dot_def]
  rcases eq_or_ne u.x 0 with hx | hx
  · rcases eq_or_ne u.y 0 with hy | hy
    · exfalso; apply h; ext <;> simp [hx, hy]
    · have : 0 < u.y * u.y := mul_self_pos.mpr hy
      nlinarith [this, hx]
  · have : 0 < u.x * u.x := mul_self_pos.mpr hx
    nlinarith [this, mul_self_nonneg u.y]

/-- A point lies on a ray iff `p - origin` is parallel to and codirectional with the
direction vector. -/
lemma mem_ray_iff (r : Ray) (p : Vector2D) :
    p ∈ r.toSet ↔ cross r.direction (vsub p r.origin) = 0 ∧
      0 ≤ dot r.direction (vsub p r.origin) := by
  constructor
  · rintro ⟨t, ht0, hx, hy⟩
    refine ⟨?_, ?_⟩
    · simp only [cross_def, vsub_x, vsub_y, hx, hy]; ring
    · simp only [dot_def, vsub_x, vsub_y, hx, hy]
      have h : r.direction.x * (r.origin.x + t * r.direction.x - r.origin.x)
             + r.direction.y * (r.origin.y + t * r.direction.y - r.origin.y)
           = t * (r.direction.x ^ 2 + r.direction.y ^ 2) := by ring
      rw [h]
      exact mul_nonneg ht0 (by positivity)
  · rintro ⟨hcross, hdot⟩
    -- direction nonzero: split on which coordinate is nonzero
    have hne := r.direction_nonzero
    rcases eq_or_ne r.direction.x 0 with hx | hx
    · -- direction.x = 0, so direction.y ≠ 0
      have hy : r.direction.y ≠ 0 := by
        intro hy; apply hne; ext <;> simp [hx, hy]
      -- cross = direction.x*(p-o).y - direction.y*(p-o).x = - direction.y*(p-o).x = 0
      -- ⇒ (p-o).x = 0
      have hpx : p.x - r.origin.x = 0 := by
        have : - r.direction.y * (p.x - r.origin.x) = 0 := by
          simpa [cross_def, hx] using hcross
        have := mul_eq_zero.1 this
        rcases this with h | h
        · exact absurd (by linarith [neg_eq_zero.1 h] : r.direction.y = 0) hy
        · exact h
      set t := (p.y - r.origin.y) / r.direction.y with ht
      refine ⟨t, ?_, ?_, ?_⟩
      · -- 0 ≤ t : from dot ≥ 0.  dot = direction.y*(p-o).y (since direction.x=0)
        have hdot' : 0 ≤ r.direction.y * (p.y - r.origin.y) := by
          simpa [dot_def, hx] using hdot
        rw [ht]
        rcases lt_or_gt_of_ne hy with hneg | hpos
        · rw [div_nonneg_iff]; right
          constructor <;> nlinarith [hdot']
        · rw [div_nonneg_iff]; left
          constructor <;> nlinarith [hdot']
      · simp only [hx, mul_zero, add_zero]; linarith [hpx]
      · rw [ht]; field_simp; ring
    · -- direction.x ≠ 0
      set t := (p.x - r.origin.x) / r.direction.x with ht
      have hpy : p.y - r.origin.y = r.direction.y * t := by
        rw [ht]; field_simp
        have : r.direction.x * (p.y - r.origin.y) = r.direction.y * (p.x - r.origin.x) := by
          have := hcross; simp only [cross_def, vsub_x, vsub_y] at this; linarith
        linarith [this]
      refine ⟨t, ?_, ?_, ?_⟩
      · -- 0 ≤ t from dot ≥ 0
        have hdot' : 0 ≤ r.direction.x * (p.x - r.origin.x)
            + r.direction.y * (p.y - r.origin.y) := by
          simpa [dot_def] using hdot
        rw [hpy] at hdot'
        -- dot = direction.x*(p-o).x + direction.y*(direction.y*t)
        --     = direction.x*(direction.x*t) + direction.y^2 t  (using (p-o).x = direction.x*t)
        have hpx : p.x - r.origin.x = r.direction.x * t := by rw [ht]; field_simp
        rw [hpx] at hdot'
        have hpos : 0 < r.direction.x ^ 2 + r.direction.y ^ 2 := by positivity
        nlinarith [hdot', hpos]
      · rw [ht]; field_simp; ring
      · linarith [hpy]

/-- A point lies on a segment iff `p - p1` is a multiple `t ∈ [0,1]` of `p2 - p1`,
expressed via cross/dot products (valid for nondegenerate segments). -/
lemma mem_seg_iff (seg : LineSegment) (p : Vector2D) :
    p ∈ seg.toSet ↔ ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧
      p.x = (1 - t) * seg.p1.x + t * seg.p2.x ∧
      p.y = (1 - t) * seg.p1.y + t * seg.p2.y := Iff.rfl

/-- The segment as `p1 + t (p2 - p1)`. -/
lemma mem_seg_iff' (seg : LineSegment) (p : Vector2D) :
    p ∈ seg.toSet ↔ ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧
      p.x = seg.p1.x + t * (seg.p2.x - seg.p1.x) ∧
      p.y = seg.p1.y + t * (seg.p2.y - seg.p1.y) := by
  rw [mem_seg_iff]
  constructor <;> rintro ⟨t, h0, h1, hx, hy⟩ <;> exact ⟨t, h0, h1, by rw [hx]; ring, by rw [hy]; ring⟩

end Polygons2
end
