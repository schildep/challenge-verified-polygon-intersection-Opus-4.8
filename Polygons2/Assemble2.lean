import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.Independence
import Polygons2.RayIndep
import Polygons2.Interior
import Polygons2.SubRay
import Polygons2.RayParam
import Polygons2.Clip
import Polygons2.InsideCount
import Polygons2.CycleDecomp
import Polygons2.GoodRay
import Polygons2.Bridge
import Polygons2.Constancy
import Polygons2.Assemble

/-!
# Assembly support for the polygon-intersection construction.

Reusable infrastructure toward `intersection_polys_aux` (assembling `polys = cycle_decomp M`):

* `exists_good_dir'` — generic forward ray from a point, non-parallel to a finite list of
  directions and missing a finite list of points (a strengthening of `GoodRay.exists_good_dir`,
  which only avoided two directions).
* `countP_subRay_eq` — sub-ray crossing count for an arbitrary segment list (the list-level
  analogue of `InsideCount.intersection_subRay_eq_countP`).
* `ray_seg_unique` — a ray meeting a non-degenerate segment whose endpoints are off the ray hits
  it in at most one point.
* `segments_ne_nil_iff` — `poly.segments ≠ [] ↔ 2 ≤ poly.vertices.length`.
* `filter_flatten_countP` — restricting `polys` to its `2 ≤ vertices.length` members (equivalently,
  its non-edgeless members) preserves the flattened crossing count.  This lets the assembly use
  `polys.filter (2 ≤ ·.vertices.length)` to obtain `2 ≤ Q.vertices.length` for every kept `Q`
  (needed for `vertex_on_boundary` and `even_odd_constancy`) without changing the parity in the
  goal's conjunct 3.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- Strengthened generic-direction lemma: a forward ray from `p` whose direction `⟨1,k⟩`
is non-parallel to every direction in the list `D` (each assumed nonzero) and which misses
every point of the list `V` (each `≠ p`). -/
lemma exists_good_dir' (p : Vector2D) (D : List Vector2D) (V : List Vector2D)
    (hD : ∀ d ∈ D, d ≠ (⟨0, 0⟩ : Vector2D)) (hpV : ∀ w ∈ V, w ≠ p) :
    ∃ k : ℚ, (∀ d ∈ D, cross d ⟨1, k⟩ ≠ 0) ∧
      (∀ w ∈ V, ¬ ∃ t : ℚ, 0 ≤ t ∧ w.x = p.x + t * 1 ∧ w.y = p.y + t * k) := by
  set Bdir : Finset ℚ := (D.map (fun d => d.y / d.x)).toFinset with hBdir
  set Bpt : Finset ℚ := (V.map (fun w => (w.y - p.y) / (w.x - p.x))).toFinset with hBpt
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset (Bdir ∪ Bpt)
  rw [Finset.mem_union, not_or] at hk
  obtain ⟨hkd, hkp⟩ := hk
  refine ⟨k, ?_, ?_⟩
  · intro d hd
    simp only [cross_def]
    rcases eq_or_ne d.x 0 with hx | hx
    · have hy : d.y ≠ 0 := fun hy => hD d hd (by ext <;> simp [hx, hy])
      simp [hx]; exact hy
    · intro hcross
      apply hkd
      rw [hBdir, List.mem_toFinset, List.mem_map]
      refine ⟨d, hd, ?_⟩
      field_simp
      linarith [hcross]
  · rintro w hw ⟨t, ht0, htx, hty⟩
    have hteq : t = w.x - p.x := by linarith [htx]
    rcases lt_trichotomy (w.x - p.x) 0 with hsign | hsign | hsign
    · rw [hteq] at ht0; linarith
    · have hwx : w.x = p.x := by linarith [hsign]
      have ht : t = 0 := by rw [hteq]; linarith [hsign]
      have hwy : w.y = p.y := by rw [hty, ht]; ring
      exact hpV w hw (by ext <;> simp [hwx, hwy])
    · apply hkp
      rw [hBpt, List.mem_toFinset, List.mem_map]
      refine ⟨w, hw, ?_⟩
      rw [hteq] at hty
      have hne : w.x - p.x ≠ 0 := ne_of_gt hsign
      field_simp
      linarith [hty]

/-- Generic sub-ray crossing count for an arbitrary segment list. -/
lemma countP_subRay_eq (r : Ray) (L : List LineSegment) {τ : ℚ} (hτ : 0 ≤ τ)
    (hnd : ∀ s ∈ L, s.p1 ≠ s.p2)
    (hoff : ∀ s ∈ L, s.p1 ∉ r.toSet ∧ s.p2 ∉ r.toSet) :
    L.countP (fun s => decide (rayIntersectsSegment (subRay r τ) s))
      = L.countP
          (fun s => decide (rayIntersectsSegment r s ∧ τ ≤ rayParam r (crossingPoint r s))) := by
  apply List.countP_congr
  intro f hf
  obtain ⟨h1, h2⟩ := hoff f hf
  have hndf := hnd f hf
  simp only [decide_eq_true_eq]
  by_cases hc : rayIntersectsSegment r f
  · rw [subRay_cross_iff r f hτ hndf h1 h2 hc]
    exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · constructor
    · intro hsub
      exact absurd (hsub.mono (Set.inter_subset_inter_left _ (subRay_toSet_subset r hτ))) hc
    · intro h; exact absurd h.1 hc

/-- If a ray's direction is non-parallel to a segment's direction and the ray avoids the
segment's endpoints, then the ray meets the segment in at most one point, and that point is
determined; in particular two common points of ray & segment coincide. -/
lemma ray_seg_unique (r : Ray) (seg : LineSegment)
    (hnd : seg.p1 ≠ seg.p2) (h1 : seg.p1 ∉ r.toSet) (h2 : seg.p2 ∉ r.toSet)
    {x y : Vector2D} (hx : x ∈ r.toSet ∩ seg.toSet) (hy : y ∈ r.toSet ∩ seg.toSet) :
    x = y := by
  have hcross : rayIntersectsSegment r seg := ⟨x, hx⟩
  have hsing := ray_seg_inter_singleton r seg hnd h1 h2 hcross
  rw [hsing] at hx hy
  rw [hx, hy]

/-- `segments` nonempty iff at least two vertices. -/
lemma segments_ne_nil_iff (poly : Polygon) :
    poly.segments ≠ [] ↔ 2 ≤ poly.vertices.length := by
  rcases hv : poly.vertices with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · rw [segs_nil hv]; simp
  · rw [segs_single hv]; simp
  · constructor
    · intro _; simp
    · intro _
      rw [segs_cons2 hv]
      simp only [ne_eq, List.map_eq_nil_iff]
      intro h
      have hz := List.length_zip (l₁ := (v0 :: v1 :: rest)) (l₂ := ((v1 :: rest) ++ [v0]))
      rw [h] at hz; simp at hz

/-- Filtering by `2 ≤ vertices.length` keeps exactly the polygons with nonempty `segments`,
hence preserves the flattened crossing count. -/
lemma filter_flatten_countP (polys : List Polygon) (q : LineSegment → Bool) :
    (((polys.filter (fun Q => decide (2 ≤ Q.vertices.length))).map
        (fun Q => Q.segments)).flatten.countP q)
      = ((polys.map (fun Q => Q.segments)).flatten.countP q) := by
  induction polys with
  | nil => simp
  | cons Q t ih =>
    by_cases h : 2 ≤ Q.vertices.length
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [List.map_cons, List.flatten_cons, List.countP_append, ih]
    · rw [List.filter_cons_of_neg (by simp [h])]
      have hseg : Q.segments = [] := by
        by_contra hne; exact h ((segments_ne_nil_iff Q).1 hne)
      simp only [List.map_cons, List.flatten_cons, List.countP_append, ih, hseg, List.countP_nil,
        Nat.zero_add]

end Polygons2
end
