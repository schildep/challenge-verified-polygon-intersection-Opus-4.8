import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.Clip
import Polygons2.Interior
import Polygons2.SubRay
import Polygons2.RayParam
import Polygons2.PairCount
import Polygons2.CrossSeq
import Polygons2.CycleDecomp

/-!
# The clipped intersection-boundary edge multiset `Mlist`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-! ## Edge parametrization -/

/-- The point on the directed segment `⟨a,b⟩` at parameter `t`. -/
def segPt (a b : Vector2D) (t : ℚ) : Vector2D :=
  ⟨(1 - t) * a.x + t * b.x, (1 - t) * a.y + t * b.y⟩

@[simp] lemma segPt_x (a b : Vector2D) (t : ℚ) :
    (segPt a b t).x = (1 - t) * a.x + t * b.x := rfl
@[simp] lemma segPt_y (a b : Vector2D) (t : ℚ) :
    (segPt a b t).y = (1 - t) * a.y + t * b.y := rfl

@[simp] lemma segPt_zero (a b : Vector2D) : segPt a b 0 = a := by
  ext <;> simp [segPt]
@[simp] lemma segPt_one (a b : Vector2D) : segPt a b 1 = b := by
  ext <;> simp [segPt]

/-- `segPt` is injective in `t` when `a ≠ b`. -/
lemma segPt_injOn {a b : Vector2D} (hab : a ≠ b) {s t : ℚ}
    (h : segPt a b s = segPt a b t) : s = t := by
  have hx : (1 - s) * a.x + s * b.x = (1 - t) * a.x + t * b.x := by
    have := congrArg Vector2D.x h; simpa using this
  have hy : (1 - s) * a.y + s * b.y = (1 - t) * a.y + t * b.y := by
    have := congrArg Vector2D.y h; simpa using this
  -- (s - t)*(b.x - a.x) = 0 and (s-t)*(b.y-a.y)=0
  have ex : (s - t) * (b.x - a.x) = 0 := by ring_nf; ring_nf at hx; linarith
  have ey : (s - t) * (b.y - a.y) = 0 := by ring_nf; ring_nf at hy; linarith
  by_contra hne
  have hst : s - t ≠ 0 := fun h0 => hne (by linarith [sub_eq_zero.1 h0])
  have hbx : b.x - a.x = 0 := by
    rcases mul_eq_zero.1 ex with h | h
    · exact absurd h hst
    · exact h
  have hby : b.y - a.y = 0 := by
    rcases mul_eq_zero.1 ey with h | h
    · exact absurd h hst
    · exact h
  exact hab (by ext <;> [linarith; linarith])

/-- A point of the segment `⟨a,b⟩` is `segPt a b t` for some `t ∈ [0,1]`. -/
lemma mem_seg_segPt {a b : Vector2D} {p : Vector2D}
    (hp : p ∈ (LineSegment.mk a b).toSet) : ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ p = segPt a b t := by
  obtain ⟨t, ht0, ht1, hx, hy⟩ := hp
  exact ⟨t, ht0, ht1, by ext <;> simp [segPt, hx, hy]⟩

/-- `segPt a b t` lies on the segment when `t ∈ [0,1]`. -/
lemma segPt_mem_seg {a b : Vector2D} {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    segPt a b t ∈ (LineSegment.mk a b).toSet :=
  ⟨t, h0, h1, rfl, rfl⟩

/-! ## Cut parameters along an edge -/

/-- The raw set of parameters `t ∈ [0,1]` where the edge `⟨a,b⟩` meets `poly`'s boundary. -/
def cutSet (a b : Vector2D) (poly : Polygon) : Set ℚ :=
  {t | 0 ≤ t ∧ t ≤ 1 ∧ segPt a b t ∈ poly.toBoundarySet}

/-- When `a ≠ b` and `poly1.toBoundarySet ∩ poly2.toBoundarySet` is finite, the cut set of
the edge `⟨a,b⟩` (assumed a poly1-edge) against `poly2` is finite, because `segPt a b ·`
injects it into the finite intersection set. -/
lemma cutSet_finite {a b : Vector2D} (hab : a ≠ b) {poly1 poly2 : Polygon}
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet)) :
    Set.Finite (cutSet a b poly2) := by
  have hpre : Set.Finite ((segPt a b) ⁻¹' (poly1.toBoundarySet ∩ poly2.toBoundarySet)) := by
    apply hfin.preimage
    intro s _ t _ h
    exact segPt_injOn hab h
  apply hpre.subset
  intro t ht
  obtain ⟨h0, h1, hb⟩ := ht
  exact ⟨hsub (segPt_mem_seg h0 h1), hb⟩

/-- The cut set as a `Finset` (empty when not finite — recovered only under hypotheses). -/
def cutFinset (a b : Vector2D) (poly : Polygon) : Finset ℚ :=
  if h : Set.Finite (cutSet a b poly) then h.toFinset else ∅

/-- The sorted list of cut parameters of `⟨a,b⟩` against `poly`, always including `0` and `1`. -/
def cutParams (a b : Vector2D) (poly : Polygon) : List ℚ :=
  Finset.sort (insert 0 (insert 1 (cutFinset a b poly)))

lemma cutParams_pairwise (a b : Vector2D) (poly : Polygon) :
    (cutParams a b poly).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort _ _

lemma cutParams_nodup (a b : Vector2D) (poly : Polygon) :
    (cutParams a b poly).Nodup :=
  Finset.sort_nodup _ _

/-- The cut parameters are strictly increasing. -/
lemma cutParams_pairwise_lt (a b : Vector2D) (poly : Polygon) :
    (cutParams a b poly).Pairwise (· < ·) := by
  have hp := cutParams_pairwise a b poly
  have hnd := cutParams_nodup a b poly
  rw [List.Nodup] at hnd
  rw [List.pairwise_iff_get] at hp hnd ⊢
  intro i j hij
  exact lt_of_le_of_ne (hp i j hij) (hnd i j hij)

lemma mem_cutParams_iff (a b : Vector2D) (poly : Polygon) (t : ℚ) :
    t ∈ cutParams a b poly ↔ t = 0 ∨ t = 1 ∨ t ∈ cutFinset a b poly := by
  unfold cutParams
  rw [Finset.mem_sort]
  simp only [Finset.mem_insert]

lemma zero_mem_cutParams (a b : Vector2D) (poly : Polygon) : (0:ℚ) ∈ cutParams a b poly := by
  rw [mem_cutParams_iff]; left; rfl

lemma one_mem_cutParams (a b : Vector2D) (poly : Polygon) : (1:ℚ) ∈ cutParams a b poly := by
  rw [mem_cutParams_iff]; right; left; rfl

/-! ## Clipping one edge -/

/-- Consecutive pairs of a list. -/
def consecPairs {α : Type*} (l : List α) : List (α × α) := l.zip l.tail

/-- The kept sub-pieces of edge `⟨a,b⟩` clipped against `other` (keep pieces whose midpoint
is in `other.interior`). -/
def clipEdge (a b : Vector2D) (other : Polygon) : List (Vector2D × Vector2D) :=
  (consecPairs (cutParams a b other)).filterMap (fun st =>
    if segPt a b ((st.1 + st.2) / 2) ∈ other.interior ∧ segPt a b st.1 ≠ segPt a b st.2 then
      some (segPt a b st.1, segPt a b st.2)
    else none)

/-- `Mlist`: clip every poly1 edge against `poly2`, every poly2 edge against `poly1`. -/
def Mlist (poly1 poly2 : Polygon) : List (Vector2D × Vector2D) :=
  (poly1.segments.flatMap (fun e => clipEdge e.p1 e.p2 poly2)) ++
  (poly2.segments.flatMap (fun f => clipEdge f.p1 f.p2 poly1))

/-- `consecPairs` membership: a member is `(l[i], l[i+1])` for consecutive indices. -/
lemma mem_consecPairs {α : Type*} {l : List α} {p : α × α} (hp : p ∈ consecPairs l) :
    ∃ i : ℕ, ∃ (h : i + 1 < l.length), p = (l[i], l[i+1]) := by
  unfold consecPairs at hp
  rw [List.mem_iff_getElem] at hp
  obtain ⟨i, hi, hgi⟩ := hp
  rw [List.length_zip, List.length_tail] at hi
  have hlt : i + 1 < l.length := by omega
  refine ⟨i, hlt, ?_⟩
  rw [← hgi, List.getElem_zip]
  congr 1
  rw [List.getElem_tail]

/-- A member of `clipEdge a b other` arises from a consecutive cut-param pair. -/
lemma mem_clipEdge {a b : Vector2D} {other : Polygon} {p : Vector2D × Vector2D}
    (hp : p ∈ clipEdge a b other) :
    ∃ s t : ℚ, s ∈ cutParams a b other ∧ t ∈ cutParams a b other ∧ s < t ∧
      (∀ u, s < u → u < t → u ∉ cutParams a b other) ∧
      segPt a b ((s + t)/2) ∈ other.interior ∧ segPt a b s ≠ segPt a b t ∧
      p = (segPt a b s, segPt a b t) := by
  unfold clipEdge at hp
  rw [List.mem_filterMap] at hp
  obtain ⟨st, hst, hfm⟩ := hp
  obtain ⟨i, hi, hsteq⟩ := mem_consecPairs hst
  have hpwlt := cutParams_pairwise_lt a b other
  rw [List.pairwise_iff_getElem] at hpwlt
  have hs1 : st.1 = (cutParams a b other)[i] := by rw [hsteq]
  have hs2 : st.2 = (cutParams a b other)[i+1] := by rw [hsteq]
  -- midpoint condition
  by_cases hmid : segPt a b ((st.1 + st.2)/2) ∈ other.interior ∧
      segPt a b st.1 ≠ segPt a b st.2
  · rw [if_pos hmid] at hfm
    have hpeq : p = (segPt a b st.1, segPt a b st.2) := by
      injection hfm with h; exact h.symm
    refine ⟨st.1, st.2, ?_, ?_, ?_, ?_, hmid.1, hmid.2, hpeq⟩
    · rw [hs1]; exact List.getElem_mem _
    · rw [hs2]; exact List.getElem_mem _
    · -- st.1 < st.2 from strict pairwise
      rw [hs1, hs2]; exact hpwlt i (i+1) (by omega) hi (by omega)
    · -- no cut param strictly between (consecutive in sorted list)
      intro u hu1 hu2 humem
      rw [hs1] at hu1
      rw [hs2] at hu2
      -- u is in L, strictly between consecutive elements: contradiction with sortedness
      rw [List.mem_iff_getElem] at humem
      obtain ⟨k, hk, hku⟩ := humem
      -- compare k with i, i+1
      rcases lt_trichotomy k i with hki | hki | hki
      · have := hpwlt k i hk (Nat.lt_of_succ_lt hi) hki
        rw [hku] at this; linarith
      · subst hki; rw [hku] at hu1; linarith
      · -- k ≥ i+1; but u < L[i+1], yet L[i+1] ≤ L[k]
        rcases lt_trichotomy k (i+1) with hk2 | hk2 | hk2
        · omega
        · subst hk2; rw [hku] at hu2; linarith
        · have := hpwlt (i+1) k hi hk hk2
          rw [hku] at this; linarith
  · rw [if_neg hmid] at hfm; exact absurd hfm (by simp)

/-- Cut parameters lie in `[0,1]`. -/
lemma cutParams_mem_Icc {a b : Vector2D} {poly : Polygon} {t : ℚ}
    (ht : t ∈ cutParams a b poly) : 0 ≤ t ∧ t ≤ 1 := by
  rw [mem_cutParams_iff] at ht
  rcases ht with h | h | h
  · subst h; exact ⟨le_refl _, by norm_num⟩
  · subst h; exact ⟨by norm_num, le_refl _⟩
  · unfold cutFinset at h
    split_ifs at h with hfin
    · rw [Set.Finite.mem_toFinset] at h; exact ⟨h.1, h.2.1⟩
    · simp at h

/-- A sub-segment `(segPt a b s, segPt a b t)` with `s,t ∈ [0,1]` lies in `⟨a,b⟩.toSet`. -/
lemma subpiece_subset {a b : Vector2D} {s t : ℚ}
    (hs : 0 ≤ s ∧ s ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) :
    (LineSegment.mk (segPt a b s) (segPt a b t)).toSet ⊆ (LineSegment.mk a b).toSet := by
  rintro x ⟨u, hu0, hu1, hx, hy⟩
  -- x = (1-u)·segPt(s) + u·segPt(t) = segPt at param (1-u)s + u t
  refine ⟨(1 - u) * s + u * t, ?_, ?_, ?_, ?_⟩
  · nlinarith [hs.1, ht.1, hu0, hu1]
  · nlinarith [hs.2, ht.2, hu0, hu1, hs.1, ht.1]
  · rw [hx]; simp only [segPt_x]; ring
  · rw [hy]; simp only [segPt_y]; ring

/-- Edge of poly ⇒ its point-set ⊆ poly's boundary. -/
lemma seg_toSet_subset_boundary {poly : Polygon} {e : LineSegment} (he : e ∈ poly.segments) :
    e.toSet ⊆ poly.toBoundarySet := by
  intro x hx; exact ⟨e, he, hx⟩

/-! ## Flip lemma: interior membership is constant along a boundary-free sub-ray segment. -/

/-- A point of `rr` at parameter `p ≥ 0` is the origin of `subRay rr p`. -/
lemma subRay_origin_mem (rr : Ray) {p : ℚ} (hp : 0 ≤ p) :
    (subRay rr p).origin ∈ rr.toSet :=
  ⟨p, hp, by simp [subRay_origin], by simp [subRay_origin]⟩

/-- The ray-parameter of `subRay rr t`'s origin is `t`. -/
lemma rayParam_subRay_origin (rr : Ray) (t : ℚ) :
    rayParam rr (subRay rr t).origin = t := by
  unfold rayParam subRay
  by_cases hdx : rr.direction.x ≠ 0
  · rw [if_pos hdx]; simp only; rw [show rr.origin.x + t * rr.direction.x - rr.origin.x
        = t * rr.direction.x from by ring, mul_div_assoc, div_self hdx, mul_one]
  · push_neg at hdx
    have hdy : rr.direction.y ≠ 0 := by
      intro h; exact rr.direction_nonzero (by ext <;> simp [hdx, h])
    rw [if_neg (by simp [hdx])]; simp only
    rw [show rr.origin.y + t * rr.direction.y - rr.origin.y
        = t * rr.direction.y from by ring, mul_div_assoc, div_self hdy, mul_one]

/-- For a poly-edge `e`, a crossing point of `subRay rr t₁` has ray-parameter `≥ t₁`. -/
lemma crossing_param_ge {rr : Ray} {t₁ : ℚ} (ht1 : 0 ≤ t₁) {e : LineSegment}
    (h : rayIntersectsSegment (subRay rr t₁) e) :
    ∃ x, x ∈ rr.toSet ∧ x ∈ e.toSet ∧ t₁ ≤ rayParam rr x := by
  obtain ⟨x, hxr, hxe⟩ := h
  have hxrr : x ∈ rr.toSet := subRay_toSet_subset rr ht1 hxr
  refine ⟨x, hxrr, hxe, ?_⟩
  exact (mem_subRay_iff rr t₁ x hxrr).1 hxr

/-- If no point of `rr` at params in `[t₁,t₂)` lies on `poly`'s boundary, then the two
sub-rays cross exactly the same poly edges. -/
lemma subRay_cross_eq {rr : Ray} {t₁ t₂ : ℚ} (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂)
    {poly : Polygon} {e : LineSegment} (he : e ∈ poly.segments)
    (hbf : ∀ x ∈ rr.toSet, rayParam rr x < t₂ → x ∉ poly.toBoundarySet) :
    rayIntersectsSegment (subRay rr t₁) e ↔ rayIntersectsSegment (subRay rr t₂) e := by
  constructor
  · intro h
    obtain ⟨x, hxrr, hxe, hxge⟩ := crossing_param_ge ht1 h
    -- x ∈ poly.boundary
    have hxbd : x ∈ poly.toBoundarySet := ⟨e, he, hxe⟩
    -- param ≥ t₂ (else boundary in forbidden range)
    have hxge2 : t₂ ≤ rayParam rr x := by
      by_contra hlt
      push_neg at hlt
      exact hbf x hxrr hlt hxbd
    refine ⟨x, ?_, hxe⟩
    exact (mem_subRay_iff rr t₂ x hxrr).2 hxge2
  · intro h
    obtain ⟨x, hxr, hxe⟩ := h
    have ht2 : 0 ≤ t₂ := le_trans ht1 ht12
    refine ⟨x, ?_, hxe⟩
    -- subRay t₂ ⊆ subRay t₁
    have hxrr : x ∈ rr.toSet := subRay_toSet_subset rr ht2 hxr
    have hge2 : t₂ ≤ rayParam rr x := (mem_subRay_iff rr t₂ x hxrr).1 hxr
    exact (mem_subRay_iff rr t₁ x hxrr).2 (le_trans ht12 hge2)

/-- The crossing counts of two sub-rays agree when the in-between is boundary-free. -/
lemma subRay_count_eq {rr : Ray} {t₁ t₂ : ℚ} (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂)
    {poly : Polygon}
    (hbf : ∀ x ∈ rr.toSet, rayParam rr x < t₂ → x ∉ poly.toBoundarySet) :
    intersectionRayPolygonSegmentsNumber (subRay rr t₁) poly
      = intersectionRayPolygonSegmentsNumber (subRay rr t₂) poly := by
  unfold intersectionRayPolygonSegmentsNumber
  apply List.countP_congr
  intro e he
  simp only [decide_eq_true_eq]
  exact subRay_cross_eq ht1 ht12 he hbf

/-- **Flip lemma (sub-ray form).** If `rr` avoids `poly`'s vertices and no point of `rr`
at parameter in `[t₁,t₂)` is on `poly`'s boundary, then the two sub-ray origins have the
same `poly.interior` status. -/
lemma flip_subRay {rr : Ray} {t₁ t₂ : ℚ} (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂)
    {poly : Polygon} (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hav : rayAvoidsVertices rr poly)
    (hbf : ∀ x ∈ rr.toSet, rayParam rr x ≤ t₂ → x ∉ poly.toBoundarySet) :
    (subRay rr t₁).origin ∈ poly.interior ↔ (subRay rr t₂).origin ∈ poly.interior := by
  have ht2 : 0 ≤ t₂ := le_trans ht1 ht12
  -- both origins are off poly's boundary
  have hoff1 : ∀ seg ∈ poly.segments, (subRay rr t₁).origin ∉ seg.toSet := by
    intro seg hseg hmem
    exact hbf _ (subRay_origin_mem rr ht1)
      (by rw [rayParam_subRay_origin]; exact ht12) ⟨seg, hseg, hmem⟩
  have hoff2 : ∀ seg ∈ poly.segments, (subRay rr t₂).origin ∉ seg.toSet := by
    intro seg hseg hmem
    exact hbf _ (subRay_origin_mem rr ht2)
      (by rw [rayParam_subRay_origin]) ⟨seg, hseg, hmem⟩
  -- boundary-free in the half-open interval for the count lemma
  have hbf' : ∀ x ∈ rr.toSet, rayParam rr x < t₂ → x ∉ poly.toBoundarySet :=
    fun x hx hlt => hbf x hx (le_of_lt hlt)
  rw [mem_interior_iff_subRay poly rr ht1 hnd hav hoff1,
      mem_interior_iff_subRay poly rr ht2 hnd hav hoff2,
      subRay_count_eq ht1 ht12 hbf']

theorem Mlist_nondeg (poly1 poly2 : Polygon) : ∀ e ∈ Mlist poly1 poly2, e.1 ≠ e.2 := by
  intro e he
  have key : ∀ (a b : Vector2D) (other : Polygon),
      e ∈ clipEdge a b other → e.1 ≠ e.2 := by
    intro a b other hce
    obtain ⟨s, t, _, _, _, _, _, hne, hpeq⟩ := mem_clipEdge hce
    rw [hpeq]; exact hne
  unfold Mlist at he
  rw [List.mem_append] at he
  rcases he with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨ed, _, hed⟩ := h
    exact key ed.p1 ed.p2 poly2 hed
  · rw [List.mem_flatMap] at h
    obtain ⟨ed, _, hed⟩ := h
    exact key ed.p1 ed.p2 poly1 hed

theorem Mlist_subset_boundary (poly1 poly2 : Polygon) :
    ∀ e ∈ Mlist poly1 poly2, ∀ x ∈ (LineSegment.mk e.1 e.2).toSet,
      x ∈ poly1.toBoundarySet ∨ x ∈ poly2.toBoundarySet := by
  intro e he x hx
  unfold Mlist at he
  rw [List.mem_append] at he
  rcases he with h | h
  · -- poly1 edge piece ⊆ poly1 boundary
    left
    rw [List.mem_flatMap] at h
    obtain ⟨ed, hed, hce⟩ := h
    obtain ⟨s, t, hs, ht, _, _, _, _, hpeq⟩ := mem_clipEdge hce
    rw [hpeq] at hx
    simp only at hx
    have hsub := subpiece_subset (a := ed.p1) (b := ed.p2)
      (cutParams_mem_Icc hs) (cutParams_mem_Icc ht) hx
    exact seg_toSet_subset_boundary (e := ⟨ed.p1, ed.p2⟩) (by
      cases ed; exact hed) hsub
  · -- poly2 edge piece ⊆ poly2 boundary
    right
    rw [List.mem_flatMap] at h
    obtain ⟨ed, hed, hce⟩ := h
    obtain ⟨s, t, hs, ht, _, _, _, _, hpeq⟩ := mem_clipEdge hce
    rw [hpeq] at hx
    simp only at hx
    have hsub := subpiece_subset (a := ed.p1) (b := ed.p2)
      (cutParams_mem_Icc hs) (cutParams_mem_Icc ht) hx
    exact seg_toSet_subset_boundary (e := ⟨ed.p1, ed.p2⟩) (by
      cases ed; exact hed) hsub

end Polygons2
end
