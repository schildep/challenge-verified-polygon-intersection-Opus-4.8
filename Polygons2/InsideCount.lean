import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.RayIndep
import Polygons2.Interior
import Polygons2.SubRay
import Polygons2.RayParam
import Polygons2.PairCount
import Polygons2.Clip
import Polygons2.Cross

/-!
# Inside-crossings parity lemma.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- A vertex-avoiding ray meets a (crossed) nondegenerate edge in exactly one point. -/
lemma ray_seg_inter_singleton (r : Ray) (seg : LineSegment)
    (hnd : seg.p1 ≠ seg.p2)
    (h1 : seg.p1 ∉ r.toSet) (h2 : seg.p2 ∉ r.toSet)
    (hcross : rayIntersectsSegment r seg) :
    r.toSet ∩ seg.toSet = {crossingPoint r seg} := by
  obtain ⟨hcr, hcs⟩ := crossingPoint_mem hcross
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨hcr, hcs⟩, ?_⟩
  -- uniqueness: any two intersection points coincide
  rintro y ⟨hyr, hys⟩
  set q := crossingPoint r seg with hq
  -- We show q = y by ruling out a "second distinct point" using crossB_iff machinery.
  -- Work with a = seg.p1, b = seg.p2.
  obtain ⟨a, b⟩ := seg
  simp only at hnd h1 h2 hcs hys ⊢
  -- crossing parameters along the ray
  obtain ⟨hqx, hqy, hq0⟩ := rayParam_spec r hcr
  obtain ⟨hyx, hyy, hy0⟩ := rayParam_spec r hyr
  -- Suppose q ≠ y. Then two distinct points of seg lie on the ray's line.
  by_contra hne
  -- both q, y on ray and on segment; use cross-product collinearity to force endpoint on ray.
  -- Set up cross signs as in crossB_iff.
  set p := r.origin with hp_def
  set d := r.direction with hd_def
  have hd0 : d ≠ ⟨0, 0⟩ := r.direction_nonzero
  set cA := cross d (vsub a p) with hcA_def
  set cB := cross d (vsub b p) with hcB_def
  -- q on segment with param u, y on segment with param v
  rw [mem_seg_iff'] at hcs hys
  simp only at hcs hys
  obtain ⟨u, hu0, hu1, hux, huy⟩ := hcs
  obtain ⟨v, hv0, hv1, hvx, hvy⟩ := hys
  -- q on ray: cross d (q - p) = 0; expand
  rw [mem_ray_iff] at hcr hyr
  obtain ⟨hqcross, hqdot⟩ := hcr
  obtain ⟨hycross, hydot⟩ := hyr
  -- cross d (q-p) = (1-u) cA + u cB = 0, similarly for v
  have hEu : (1 - u) * cA + u * cB = 0 := by
    have : cross d (vsub q p) = (1 - u) * cA + u * cB := by
      rw [hcA_def, hcB_def]
      simp only [cross_def, vsub_x, vsub_y, hux, huy]; ring
    rw [← this]; exact hqcross
  have hEv : (1 - v) * cA + v * cB = 0 := by
    have : cross d (vsub y p) = (1 - v) * cA + v * cB := by
      rw [hcA_def, hcB_def]
      simp only [cross_def, vsub_x, vsub_y, hvx, hvy]; ring
    rw [← this]; exact hycross
  -- Endpoints off ray ⇒ cA ≠ 0, cB ≠ 0 (else endpoint on ray's line and on ray).
  -- cA = 0 ⇒ a on ray's line; combined with dot, contradiction with a ∉ r.toSet unless dot<0.
  -- We instead show u = v, contradicting q ≠ y.
  -- From hEu - hEv: (u - v)(cB - cA) = 0.
  have hsub : (u - v) * (cB - cA) = 0 := by nlinarith [hEu, hEv]
  -- Case cB = cA: then hEu gives cA = 0 (since (1-u)+u=1); leads to both endpoints having cross 0.
  rcases mul_eq_zero.1 hsub with huv | hcAB
  · -- u = v ⇒ q = y, contradiction
    have huv' : u = v := by linarith
    apply hne
    apply Vector2D.ext
    · rw [hux, hvx, huv']
    · rw [huy, hvy, huv']
  · -- cB = cA. Then hEu: (1-u)cA + u cA = cA = 0, so cA = cB = 0.
    have hcAeq : cB = cA := by linarith
    have hcA0 : cA = 0 := by nlinarith [hEu, hcAeq]
    have hcB0 : cB = 0 := by rw [hcAeq]; exact hcA0
    -- a ∉ ray ⇒ since cross d (a-p) = cA = 0, must have dot d (a-p) < 0.
    have hdotA_neg : dot d (vsub a p) < 0 := by
      by_contra hcon
      rw [not_lt] at hcon
      apply h1
      rw [mem_ray_iff]; exact ⟨by rw [← hcA_def]; exact hcA0, hcon⟩
    have hdotB_neg : dot d (vsub b p) < 0 := by
      by_contra hcon
      rw [not_lt] at hcon
      apply h2
      rw [mem_ray_iff]; exact ⟨by rw [← hcB_def]; exact hcB0, hcon⟩
    -- q on ray: dot d (q - p) ≥ 0; but it equals (1-u) dotA + u dotB < 0. Contradiction.
    have hdotq : dot d (vsub q p) = (1 - u) * dot d (vsub a p) + u * dot d (vsub b p) := by
      simp only [dot_def, vsub_x, vsub_y, hux, huy]; ring
    rw [hdotq] at hqdot
    have hc1 : (1 - u) * dot d (vsub a p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hdotA_neg)
    have hc2 : u * dot d (vsub b p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0 (le_of_lt hdotB_neg)
    -- one of the coefficients is strictly positive
    rcases le_or_gt u 0 with hu | hu
    · have hu' : u = 0 := le_antisymm hu hu0
      rw [hu'] at hqdot
      nlinarith [hqdot, hdotA_neg]
    · nlinarith [hqdot, hc1, hu, hdotB_neg]

/-- Segment endpoints of a polygon are off a vertex-avoiding ray. -/
lemma seg_endpoints_off_ray {poly : Polygon} {r : Ray} (hav : rayAvoidsVertices r poly)
    {seg : LineSegment} (hs : seg ∈ poly.segments) :
    seg.p1 ∉ r.toSet ∧ seg.p2 ∉ r.toSet := by
  obtain ⟨hm1, hm2⟩ := seg_mem_vertices hs
  exact ⟨vertex_not_on_ray hav hm1, vertex_not_on_ray hav hm2⟩

/-- Sub-lemma B: for a crossed edge `f`, the sub-ray at `t ≥ 0` crosses `f`
iff `t ≤ rayParam r (crossingPoint r f)`. -/
lemma subRay_cross_iff (r : Ray) (f : LineSegment) {t : ℚ} (ht : 0 ≤ t)
    (hnd : f.p1 ≠ f.p2) (h1 : f.p1 ∉ r.toSet) (h2 : f.p2 ∉ r.toSet)
    (hcross : rayIntersectsSegment r f) :
    rayIntersectsSegment (subRay r t) f ↔ t ≤ rayParam r (crossingPoint r f) := by
  obtain ⟨hcr, hcs⟩ := crossingPoint_mem hcross
  have hsing := ray_seg_inter_singleton r f hnd h1 h2 hcross
  constructor
  · rintro ⟨z, hzr, hzs⟩
    -- z ∈ subRay ⊆ r, and z ∈ f, so z ∈ r ∩ f = {crossingPoint}; thus z = crossingPoint
    have hzr' : z ∈ r.toSet := subRay_toSet_subset r ht hzr
    have : z ∈ r.toSet ∩ f.toSet := ⟨hzr', hzs⟩
    rw [hsing] at this
    have hz_eq : z = crossingPoint r f := this
    rw [← hz_eq]
    rw [← (mem_subRay_iff r t z hzr')]
    exact hzr
  · intro hle
    -- crossingPoint ∈ subRay (by mem_subRay_iff) and ∈ f, so subRay crosses f
    refine ⟨crossingPoint r f, ?_, hcs⟩
    rw [mem_subRay_iff r t (crossingPoint r f) hcr]
    exact hle

/-- Sub-lemma C: the number of poly2 edges crossed by `subRay r τ` equals the number of
crossing-parameters that are `≥ τ`. -/
lemma intersection_subRay_eq_countP (r : Ray) (poly : Polygon) {τ : ℚ} (hτ : 0 ≤ τ)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2) (hav : rayAvoidsVertices r poly) :
    intersectionRayPolygonSegmentsNumber (subRay r τ) poly
      = poly.segments.countP
          (fun f => decide (rayIntersectsSegment r f ∧ τ ≤ rayParam r (crossingPoint r f))) := by
  unfold intersectionRayPolygonSegmentsNumber
  apply List.countP_congr
  intro f hf
  obtain ⟨h1, h2⟩ := seg_endpoints_off_ray hav hf
  have hndf := hnd f hf
  simp only [decide_eq_true_eq]
  by_cases hc : rayIntersectsSegment r f
  · rw [subRay_cross_iff r f hτ hndf h1 h2 hc]
    constructor
    · intro h; exact ⟨hc, h⟩
    · intro h; exact h.2
  · constructor
    · intro hsub
      exact absurd (hsub.mono (Set.inter_subset_inter_left _ (subRay_toSet_subset r hτ))) hc
    · intro h; exact absurd h.1 hc

/-- A crossed edge's crossing point reconstructs the sub-ray origin. -/
lemma crossingPoint_eq_subRay_origin (r : Ray) {seg : LineSegment}
    (hcross : rayIntersectsSegment r seg) :
    crossingPoint r seg = (subRay r (rayParam r (crossingPoint r seg))).origin := by
  obtain ⟨hcr, _⟩ := crossingPoint_mem hcross
  obtain ⟨hx, hy, _⟩ := rayParam_spec r hcr
  apply Vector2D.ext
  · simp only [subRay_origin]; exact hx
  · simp only [subRay_origin]; exact hy

/-- Inside ⇔ odd-beyond. -/
lemma inside_iff_odd_beyond (poly1 poly2 : Polygon) (r : Ray) (e : LineSegment)
    (he : e ∈ poly1.segments) (hce : rayIntersectsSegment r e)
    (hnd2 : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (hav2 : rayAvoidsVertices r poly2)
    (hS : ∀ x ∈ r.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False) :
    crossingPoint r e ∈ poly2.interior ↔
      (poly2.segments.countP
        (fun f => decide (rayIntersectsSegment r f
          ∧ rayParam r (crossingPoint r e) ≤ rayParam r (crossingPoint r f)))) % 2 = 1 := by
  set q := crossingPoint r e with hq
  obtain ⟨hcr, hcs⟩ := crossingPoint_mem hce
  obtain ⟨hqx, hqy, hτ0⟩ := rayParam_spec r hcr
  set τ := rayParam r q with hτdef
  have hqeq : q = (subRay r τ).origin := crossingPoint_eq_subRay_origin r hce
  have hqb1 : q ∈ poly1.toBoundarySet := ⟨e, he, hcs⟩
  have hoff : ∀ seg ∈ poly2.segments, (subRay r τ).origin ∉ seg.toSet := by
    intro seg hseg hmem
    rw [← hqeq] at hmem
    exact hS q hcr hqb1 ⟨seg, hseg, hmem⟩
  have hiff := mem_interior_iff_subRay poly2 r hτ0 hnd2 hav2 hoff
  rw [← hqeq] at hiff
  rw [hiff, intersection_subRay_eq_countP r poly2 hτ0 hnd2 hav2]

/-- `countP p ≡ Σ g (mod 2)` when termwise indicator parity matches. -/
lemma countP_modEq_sum_map {α : Type*} (p : α → Bool) (g : α → ℕ) (l : List α)
    (h : ∀ a ∈ l, (if p a then 1 else 0) % 2 = g a % 2) :
    l.countP p % 2 = (l.map g).sum % 2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self ..)
    have iht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    by_cases hp : p a <;> simp only [hp, if_true] at ha ⊢ <;> omega

/-- `rayParam` is injective on points of the ray. -/
lemma rayParam_inj (r : Ray) {x y : Vector2D} (hx : x ∈ r.toSet) (hy : y ∈ r.toSet)
    (h : rayParam r x = rayParam r y) : x = y := by
  obtain ⟨hxx, hxy, _⟩ := rayParam_spec r hx
  obtain ⟨hyx, hyy, _⟩ := rayParam_spec r hy
  apply Vector2D.ext
  · rw [hxx, hyx, h]
  · rw [hxy, hyy, h]

/-- Sum over a filtered-then-mapped list equals sum of guarded values over the whole list. -/
lemma sum_map_filter_eq {α : Type*} (p : α → Bool) (h : α → ℕ) (l : List α) :
    (((l.filter p).map h).sum : ℕ)
      = (l.map (fun a => if p a then h a else 0)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filter_cons]
    by_cases hp : p a
    · simp only [hp, if_true, List.map_cons, List.sum_cons, ih]
    · simp only [hp, if_false, List.map_cons, List.sum_cons, Bool.false_eq_true]
      simp [ih]

/-- The list of poly's crossing parameters. -/
def crossParams (r : Ray) (poly : Polygon) : List ℚ :=
  (poly.segments.filter (fun f => decide (rayIntersectsSegment r f))).map
    (fun f => rayParam r (crossingPoint r f))

lemma crossParams_length (r : Ray) (poly : Polygon) :
    (crossParams r poly).length = intersectionRayPolygonSegmentsNumber r poly := by
  unfold crossParams intersectionRayPolygonSegmentsNumber
  rw [List.length_map, ← List.countP_eq_length_filter]

/-- The beyond-count over `poly.segments` equals the `countP` over the crossing parameters. -/
lemma countP_beyond_eq (r : Ray) (poly : Polygon) (τ : ℚ) :
    (crossParams r poly).countP (fun u => decide (τ ≤ u))
      = poly.segments.countP
          (fun f => decide (rayIntersectsSegment r f ∧ τ ≤ rayParam r (crossingPoint r f))) := by
  unfold crossParams
  rw [List.countP_map, List.countP_filter]
  apply List.countP_congr
  intro f _
  simp only [Function.comp, decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- Disjointness of the two crossing-parameter lists. -/
lemma crossParams_disjoint (poly1 poly2 : Polygon) (r : Ray)
    (hS : ∀ x ∈ r.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False) :
    ∀ x ∈ crossParams r poly1, ∀ y ∈ crossParams r poly2, x ≠ y := by
  intro x hx y hy hxy
  unfold crossParams at hx hy
  rw [List.mem_map] at hx hy
  obtain ⟨e, he, hex⟩ := hx
  obtain ⟨f, hf, hfy⟩ := hy
  rw [List.mem_filter] at he hf
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hf1, hf2⟩ := hf
  simp only [decide_eq_true_eq] at he2 hf2
  obtain ⟨hcre, hcse⟩ := crossingPoint_mem he2
  obtain ⟨hcrf, hcsf⟩ := crossingPoint_mem hf2
  -- rayParam r (crossingPoint r e) = rayParam r (crossingPoint r f)
  have hparam : rayParam r (crossingPoint r e) = rayParam r (crossingPoint r f) := by
    rw [hex, hfy]; exact hxy
  have hpts : crossingPoint r e = crossingPoint r f := rayParam_inj r hcre hcrf hparam
  -- crossing point is on both boundaries and on the ray
  apply hS (crossingPoint r e) hcre ⟨e, he1, hcse⟩
  rw [hpts]; exact ⟨f, hf1, hcsf⟩

theorem insideCrossings_parity (poly1 poly2 : Polygon) (r : Ray)
    (hnd1 : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (hnd2 : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (hav1 : rayAvoidsVertices r poly1) (hav2 : rayAvoidsVertices r poly2)
    (hS : ∀ x ∈ r.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False) :
    insideCrossings r poly1 poly2 % 2
      = (intersectionRayPolygonSegmentsNumber r poly1 % 2)
        * (intersectionRayPolygonSegmentsNumber r poly2 % 2) := by
  set L1 := crossParams r poly1 with hL1
  set L2 := crossParams r poly2 with hL2
  -- symmetric version of hS
  have hS' : ∀ x ∈ r.toSet, x ∈ poly2.toBoundarySet → x ∈ poly1.toBoundarySet → False :=
    fun x hx h2 h1 => hS x hx h1 h2
  -- The two terms of insideCrossings, related mod 2 to the sums.
  -- Term 1 (poly1 edges, inside poly2).
  have hT1 : (poly1.segments.countP
      (fun e => decide (rayIntersectsSegment r e ∧ crossingPoint r e ∈ poly2.interior))) % 2
      = (L1.map (fun τ => L2.countP (fun u => decide (τ ≤ u)))).sum % 2 := by
    rw [countP_modEq_sum_map
        (fun e => decide (rayIntersectsSegment r e ∧ crossingPoint r e ∈ poly2.interior))
        (fun e => if decide (rayIntersectsSegment r e) then
          L2.countP (fun u => decide (rayParam r (crossingPoint r e) ≤ u)) else 0)
        poly1.segments ?_]
    · -- rewrite the sum over poly1.segments to the sum over L1
      rw [hL1]; unfold crossParams
      rw [List.map_map]
      rw [← sum_map_filter_eq (fun e => decide (rayIntersectsSegment r e))
        (fun e => L2.countP (fun u => decide (rayParam r (crossingPoint r e) ≤ u))) poly1.segments]
      rfl
    · intro e he
      by_cases hc : rayIntersectsSegment r e
      · simp only [hc, decide_true, if_true, decide_eq_true_eq]
        have hiff := inside_iff_odd_beyond poly1 poly2 r e he hc hnd2 hav2 hS
        rw [hL2, countP_beyond_eq r poly2 (rayParam r (crossingPoint r e))]
        by_cases hin : crossingPoint r e ∈ poly2.interior
        · have h1 := hiff.1 hin
          rw [if_pos ⟨trivial, hin⟩]; omega
        · have hno : ¬ ((poly2.segments.countP (fun f => decide (rayIntersectsSegment r f ∧ rayParam r (crossingPoint r e) ≤ rayParam r (crossingPoint r f)))) % 2 = 1) := fun h => hin (hiff.2 h)
          rw [if_neg (fun hp => hin hp.2)]; omega
      · simp only [hc, decide_false, if_false, false_and, Bool.false_eq_true]
  -- Term 2 (poly2 edges, inside poly1), symmetric.
  have hT2 : (poly2.segments.countP
      (fun f => decide (rayIntersectsSegment r f ∧ crossingPoint r f ∈ poly1.interior))) % 2
      = (L2.map (fun τ => L1.countP (fun u => decide (τ ≤ u)))).sum % 2 := by
    rw [countP_modEq_sum_map
        (fun f => decide (rayIntersectsSegment r f ∧ crossingPoint r f ∈ poly1.interior))
        (fun f => if decide (rayIntersectsSegment r f) then
          L1.countP (fun u => decide (rayParam r (crossingPoint r f) ≤ u)) else 0)
        poly2.segments ?_]
    · rw [hL2]; unfold crossParams
      rw [List.map_map]
      rw [← sum_map_filter_eq (fun f => decide (rayIntersectsSegment r f))
        (fun f => L1.countP (fun u => decide (rayParam r (crossingPoint r f) ≤ u))) poly2.segments]
      rfl
    · intro f hf
      by_cases hc : rayIntersectsSegment r f
      · simp only [hc, decide_true, if_true, decide_eq_true_eq]
        have hiff := inside_iff_odd_beyond poly2 poly1 r f hf hc hnd1 hav1 hS'
        rw [hL1, countP_beyond_eq r poly1 (rayParam r (crossingPoint r f))]
        by_cases hin : crossingPoint r f ∈ poly1.interior
        · have h1 := hiff.1 hin
          rw [if_pos ⟨trivial, hin⟩]; omega
        · rw [if_neg (fun hp => hin hp.2)]
          have hno : ¬ ((poly1.segments.countP (fun g => decide (rayIntersectsSegment r g ∧ rayParam r (crossingPoint r f) ≤ rayParam r (crossingPoint r g)))) % 2 = 1) := fun h => hin (hiff.2 h)
          omega
      · simp only [hc, decide_false, if_false, false_and, Bool.false_eq_true]
  -- Convert ≤ to < using disjointness.
  have hdisj := crossParams_disjoint poly1 poly2 r hS
  have hconv1 : (L1.map (fun τ => L2.countP (fun u => decide (τ ≤ u)))).sum
      = (L1.map (fun τ => L2.countP (fun u => decide (τ < u)))).sum := by
    apply congrArg
    apply List.map_congr_left
    intro τ hτ
    apply List.countP_congr
    intro u hu
    have hne : τ ≠ u := hdisj τ hτ u hu
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact lt_of_le_of_ne h hne
    · intro h; exact le_of_lt h
  have hconv2 : (L2.map (fun τ => L1.countP (fun u => decide (τ ≤ u)))).sum
      = (L2.map (fun u => L1.countP (fun x => decide (u < x)))).sum := by
    apply congrArg
    apply List.map_congr_left
    intro u hu
    apply List.countP_congr
    intro x hx
    have hne : x ≠ u := hdisj x hx u hu
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact lt_of_le_of_ne h (Ne.symm hne)
    · intro h; exact le_of_lt h
  -- Assemble.
  have hpair := pair_count L1 L2 hdisj
  have hlen : L1.length * L2.length
      = intersectionRayPolygonSegmentsNumber r poly1 * intersectionRayPolygonSegmentsNumber r poly2 := by
    rw [hL1, hL2, crossParams_length, crossParams_length]
  -- combine T1 + T2 mod 2 into the pair-count
  have hsum : ((L1.map (fun τ => L2.countP (fun u => decide (τ ≤ u)))).sum
      + (L2.map (fun τ => L1.countP (fun u => decide (τ ≤ u)))).sum)
      = intersectionRayPolygonSegmentsNumber r poly1 * intersectionRayPolygonSegmentsNumber r poly2 := by
    rw [hconv1, hconv2, hpair, hlen]
  -- insideCrossings = T1 + T2
  have hic : insideCrossings r poly1 poly2 % 2
      = (intersectionRayPolygonSegmentsNumber r poly1
          * intersectionRayPolygonSegmentsNumber r poly2) % 2 := by
    unfold insideCrossings
    rw [Nat.add_mod, hT1, hT2, ← Nat.add_mod, hsum]
  rw [hic, Nat.mul_mod]
  have h1 : intersectionRayPolygonSegmentsNumber r poly1 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : intersectionRayPolygonSegmentsNumber r poly2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases hh : intersectionRayPolygonSegmentsNumber r poly1 % 2 <;>
    interval_cases hk : intersectionRayPolygonSegmentsNumber r poly2 % 2 <;> rfl

end Polygons2
end
