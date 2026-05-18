import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

/-!
# Polygon Intersection: Definitions

Self-contained definitions needed to state
`exists_polygons_inter_interior_eq_symmDiffAll_interiors_sdiff_boundaries`.
-/

open Classical Set

noncomputable section

namespace Polygons2

/-- A 2D vector with rational coordinates. -/
@[ext]
structure Vector2D where
  x : ℚ
  y : ℚ
  deriving DecidableEq, Repr, Inhabited

/-- A line segment defined by two endpoints. -/
structure LineSegment where
  p1 : Vector2D
  p2 : Vector2D
  deriving Repr

/-- A ray defined by an origin point and a direction vector. -/
structure Ray where
  origin : Vector2D
  direction : Vector2D
  direction_nonzero : direction ≠ ⟨0, 0⟩

/-- Convert a line segment to the set of points it contains. -/
def LineSegment.toSet (seg : LineSegment) : Set Vector2D :=
  { p : Vector2D |
    ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧
      p.x = (1 - t) * seg.p1.x + t * seg.p2.x ∧
      p.y = (1 - t) * seg.p1.y + t * seg.p2.y }

/-- Convert a ray to the set of points it contains. -/
def Ray.toSet (r : Ray) : Set Vector2D :=
  { p : Vector2D |
    ∃ t : ℚ, 0 ≤ t ∧
      p.x = r.origin.x + t * r.direction.x ∧
      p.y = r.origin.y + t * r.direction.y }

/-- A polygon defined by a list of vertices. -/
structure Polygon where
  vertices : List Vector2D

/-- The set of vertices of a polygon. -/
def Polygon.toVertices (poly : Polygon) : Set Vector2D :=
  { p : Vector2D | p ∈ poly.vertices }

/-- Get the list of line segments forming the boundary of a polygon. -/
def Polygon.segments (poly : Polygon) : List LineSegment :=
  match poly.vertices with
  | [] => []
  | [_] => []
  | v :: vs =>
    let pairs := List.zip (v :: vs) (vs ++ [v])
    pairs.map fun (a, b) => ⟨a, b⟩

/-- The boundary of a polygon: the union of all segment sets. -/
def Polygon.toBoundarySet (poly : Polygon) : Set Vector2D :=
  { p : Vector2D | ∃ seg ∈ poly.segments, p ∈ seg.toSet }

/-- Check if a ray intersects a line segment. -/
def rayIntersectsSegment (r : Ray) (seg : LineSegment) : Prop :=
  (r.toSet ∩ seg.toSet).Nonempty

/-- The number of line segments of a polygon that a ray intersects. -/
noncomputable def intersectionRayPolygonSegmentsNumber (r : Ray) (poly : Polygon) : ℕ :=
  poly.segments.countP fun seg => decide (rayIntersectsSegment r seg)

/-- Predicate stating that a ray does not pass through any vertex of a polygon. -/
def rayAvoidsVertices (r : Ray) (poly : Polygon) : Prop :=
  r.toSet ∩ poly.toVertices = ∅

/-- A point avoids a line segment (not on the segment). -/
def pointAvoidsSegment (p : Vector2D) (seg : LineSegment) : Prop :=
  p ∉ seg.toSet

/-- The interior of a polygon: the set of points not on any edge such that
    every ray from the point that avoids the polygon's vertices
    intersects an odd number of polygon segments. -/
def Polygon.interior (poly : Polygon) : Set Vector2D :=
  { p : Vector2D |
    (∀ seg ∈ poly.segments, pointAvoidsSegment p seg) ∧
    ∀ r : Ray, r.origin = p → rayAvoidsVertices r poly →
      intersectionRayPolygonSegmentsNumber r poly % 2 = 1 }

/-- The symmetric difference of a list of sets, defined by folding the binary
    symmetric difference starting from `∅`. -/
def symmDiffAll {α : Type*} (l : List (Set α)) : Set α :=
  l.foldr symmDiff ∅

end Polygons2

end
