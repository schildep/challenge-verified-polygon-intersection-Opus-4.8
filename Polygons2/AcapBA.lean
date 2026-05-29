import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.RayIndep
import Polygons2.Interior
import Polygons2.SubRay
import Polygons2.RayParam
import Polygons2.Clip
import Polygons2.ClipM
import Polygons2.Constancy
import Polygons2.InsideCount
import Polygons2.ClipProps
import Polygons2.ClipDegree

/-!
# Local constancy of `interior poly1 ∩ interior poly2` across an `Mlist`-free segment.

If the closed segment `[p,q]` misses every edge of `Mlist poly1 poly2`, then membership in
`poly1.interior ∩ poly2.interior` is the same at `p` and `q`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-! ## A "good leg": a segment that is well-behaved for the inside-constancy argument. -/

/-- The set of parameters `t ∈ (0,1]` whose point on `[A,B]` lies on `poly1` or `poly2`'s
boundary. -/
def bdyParams (A B : Vector2D) (poly1 poly2 : Polygon) : Set ℚ :=
  {t | 0 < t ∧ t ≤ 1 ∧ segPt A B t ∈ poly1.toBoundarySet ∪ poly2.toBoundarySet}

/-! ## At most one crossing parameter for a non-parallel edge -/

/-- If `B-A` is not parallel to `b-a`, then there is at most one `t` with
`segPt A B t` on the edge `[a,b]`. -/
lemma segPt_mem_unique_of_cross {A B a b : Vector2D}
    (hcr : cross (vsub B A) (vsub b a) ≠ 0)
    {s t : ℚ} (hs : segPt A B s ∈ (LineSegment.mk a b).toSet)
    (ht : segPt A B t ∈ (LineSegment.mk a b).toSet) : s = t := by
  obtain ⟨us, _, _, hsx, hsy⟩ := hs
  obtain ⟨ut, _, _, htx, hty⟩ := ht
  -- segPt A B s = (1-us) a + us b
  simp only [segPt_x, segPt_y] at hsx hsy htx hty
  -- Subtracting the two equations: A + s(B-A) - (A + t(B-A)) = (us-ut)·(b-a)... in each coord.
  -- (s - t)(B.x - A.x) = (us - ut)(b.x - a.x), similarly y.
  have ex : (s - t) * (B.x - A.x) = (us - ut) * (b.x - a.x) := by
    have h1 : (1 - s) * A.x + s * B.x = (1 - us) * a.x + us * b.x := hsx
    have h2 : (1 - t) * A.x + t * B.x = (1 - ut) * a.x + ut * b.x := htx
    nlinarith [h1, h2]
  have ey : (s - t) * (B.y - A.y) = (us - ut) * (b.y - a.y) := by
    have h1 : (1 - s) * A.y + s * B.y = (1 - us) * a.y + us * b.y := hsy
    have h2 : (1 - t) * A.y + t * B.y = (1 - ut) * a.y + ut * b.y := hty
    nlinarith [h1, h2]
  -- eliminate (us-ut): (s-t)·cross(B-A, b-a) = 0
  have hkey : (s - t) * cross (vsub B A) (vsub b a) = 0 := by
    simp only [cross_def, vsub_x, vsub_y]
    linear_combination (b.y - a.y) * ex - (b.x - a.x) * ey
  rcases mul_eq_zero.mp hkey with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h hcr

/-! ## Goodness of a leg direction: non-parallel to every edge -/

/-- A direction `B - A` is *transversal* to `poly` if it is non-parallel to each of `poly`'s
edges. -/
def transversalTo (A B : Vector2D) (poly : Polygon) : Prop :=
  ∀ e ∈ poly.segments, cross (vsub B A) (vsub e.p2 e.p1) ≠ 0

/-- For a transversal direction, each edge contributes at most one crossing parameter, so the
preimage of the boundary is finite. -/
lemma boundary_preimage_finite {A B : Vector2D} {poly : Polygon}
    (htr : transversalTo A B poly) :
    Set.Finite ((segPt A B) ⁻¹' poly.toBoundarySet) := by
  -- cover by the finite union over edges
  have hsub : (segPt A B) ⁻¹' poly.toBoundarySet
      ⊆ ⋃ e ∈ poly.segments, (segPt A B) ⁻¹' e.toSet := by
    intro t ht
    obtain ⟨e, he, hte⟩ := ht
    simp only [Set.mem_iUnion]
    exact ⟨e, he, hte⟩
  refine Set.Finite.subset ?_ hsub
  apply Set.Finite.biUnion poly.segments.finite_toSet
  intro e he
  -- preimage of e.toSet under segPt is a subsingleton (≤ 1 element)
  apply Set.Subsingleton.finite
  intro s hs t ht
  have hcr : cross (vsub B A) (vsub e.p2 e.p1) ≠ 0 := htr e he
  have hs' : segPt A B s ∈ (LineSegment.mk e.p1 e.p2).toSet := by
    cases e; exact hs
  have ht' : segPt A B t ∈ (LineSegment.mk e.p1 e.p2).toSet := by
    cases e; exact ht
  exact segPt_mem_unique_of_cross hcr hs' ht'

/-- For transversal directions to both polygons, the set `bdyParams` is finite. -/
lemma bdyParams_finite {A B : Vector2D} {poly1 poly2 : Polygon}
    (htr1 : transversalTo A B poly1) (htr2 : transversalTo A B poly2) :
    Set.Finite (bdyParams A B poly1 poly2) := by
  have h1 := boundary_preimage_finite htr1
  have h2 := boundary_preimage_finite htr2
  refine Set.Finite.subset (h1.union h2) ?_
  intro t ht
  obtain ⟨_, _, hb⟩ := ht
  rcases hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr hb

/-! ## Constancy on a boundary-free prefix of `[A,B]` -/

/-- A point of the segment `[A, segPt A B t']` equals `segPt A B w` for some `w ∈ [0, t']`. -/
lemma mem_prefix_segPt {A B : Vector2D} {t' : ℚ} (ht'0 : 0 ≤ t')
    {x : Vector2D} (hx : x ∈ (LineSegment.mk A (segPt A B t')).toSet) :
    ∃ w, 0 ≤ w ∧ w ≤ t' ∧ x = segPt A B w := by
  obtain ⟨u, hu0, hu1, hxx, hxy⟩ := hx
  -- x = (1-u) A + u (segPt A B t') = segPt A B (u * t')
  refine ⟨u * t', mul_nonneg hu0 ht'0, ?_, ?_⟩
  · nlinarith [hu1, ht'0, hu0]
  · ext
    · rw [hxx]; simp only [segPt_x]; ring
    · rw [hxy]; simp only [segPt_y]; ring

/-- If `A = segPt A B 0` is off both boundaries and no parameter in `(0, t']` is a boundary
parameter, then the segment `[A, segPt A B t']` misses `poly`'s boundary. -/
lemma prefix_boundary_free {A B : Vector2D} {poly1 poly2 : Polygon} {t' : ℚ}
    (ht'0 : 0 ≤ t')
    (hA1 : A ∉ poly1.toBoundarySet) (hA2 : A ∉ poly2.toBoundarySet)
    (hfree : ∀ w, 0 < w → w ≤ t' →
      segPt A B w ∉ poly1.toBoundarySet ∧ segPt A B w ∉ poly2.toBoundarySet) :
    (∀ x ∈ (LineSegment.mk A (segPt A B t')).toSet, x ∉ poly1.toBoundarySet)
      ∧ (∀ x ∈ (LineSegment.mk A (segPt A B t')).toSet, x ∉ poly2.toBoundarySet) := by
  have key : ∀ x ∈ (LineSegment.mk A (segPt A B t')).toSet,
      x ∉ poly1.toBoundarySet ∧ x ∉ poly2.toBoundarySet := by
    intro x hx
    obtain ⟨w, hw0, hwt, hxw⟩ := mem_prefix_segPt ht'0 hx
    rcases eq_or_lt_of_le hw0 with hw0eq | hw0lt
    · -- w = 0, x = A
      have : x = A := by rw [hxw, ← hw0eq]; exact segPt_zero A B
      rw [this]; exact ⟨hA1, hA2⟩
    · rw [hxw]; exact hfree w hw0lt hwt
  exact ⟨fun x hx => (key x hx).1, fun x hx => (key x hx).2⟩

/-! ## Genericity: choosing a perturbation `k` making both legs transversal -/

/-- `cross (R-p) d` as an affine function of `k`, where `R = Rrat p q k`. -/
lemma cross_leg1_eq (p q d : Vector2D) (k : ℚ) :
    cross (vsub (Rrat p q k) p) d
      = (cross (vsub q p) d)/2 + k * (cross ⟨q.y-p.y, -(q.x-p.x)⟩ d) := by
  unfold Rrat vsub cross; simp; ring

lemma cross_leg2_eq (p q d : Vector2D) (k : ℚ) :
    cross (vsub q (Rrat p q k)) d
      = (cross (vsub q p) d)/2 - k * (cross ⟨q.y-p.y, -(q.x-p.x)⟩ d) := by
  unfold Rrat vsub cross; simp; ring

/-- For `p ≠ q` and a nondegenerate edge direction `d`, the perpendicular cross-term is nonzero
whenever the parallel one is — i.e. not both vanish. -/
lemma not_both_cross_zero {p q d : Vector2D} (hpq : p ≠ q) (hd : d ≠ ⟨0,0⟩)
    (h1 : cross (vsub q p) d = 0) : cross ⟨q.y-p.y, -(q.x-p.x)⟩ d ≠ 0 := by
  intro h2
  -- both cross(q-p,d)=0 and cross(perp,d)=0 ⇒ d parallel to both q-p and its perp ⇒ d=0
  -- cross(q-p,d) = (q.x-p.x)d.y - (q.y-p.y)d.x = 0
  -- cross(perp,d) = (q.y-p.y)d.y + (q.x-p.x)d.x = 0
  simp only [cross_def, vsub_x, vsub_y] at h1 h2
  -- so ((q.x-p.x)^2+(q.y-p.y)^2) d.x = 0 and similarly d.y = 0
  have hpqne : (q.x - p.x)^2 + (q.y - p.y)^2 ≠ 0 := by
    intro h
    apply hpq
    have hx : q.x - p.x = 0 := by nlinarith [sq_nonneg (q.x-p.x), sq_nonneg (q.y-p.y), h]
    have hy : q.y - p.y = 0 := by nlinarith [sq_nonneg (q.x-p.x), sq_nonneg (q.y-p.y), h]
    ext <;> [linarith; linarith]
  have hdx : ((q.x-p.x)^2 + (q.y-p.y)^2) * d.x = 0 := by
    linear_combination (q.x-p.x) * h2 - (q.y-p.y) * h1
  have hdy : ((q.x-p.x)^2 + (q.y-p.y)^2) * d.y = 0 := by
    linear_combination (q.x-p.x) * h1 + (q.y-p.y) * h2
  apply hd
  ext
  · rcases mul_eq_zero.mp hdx with h | h
    · exact absurd h hpqne
    · exact h
  · rcases mul_eq_zero.mp hdy with h | h
    · exact absurd h hpqne
    · exact h

/-- There is a finite set of `k` outside which both legs are transversal to `poly`. -/
lemma exists_transversal_bad_k (p q : Vector2D) (hpq : p ≠ q) (poly : Polygon)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2) :
    ∃ B : Finset ℚ, ∀ k : ℚ, k ∉ B →
      transversalTo p (Rrat p q k) poly ∧ transversalTo (Rrat p q k) q poly := by
  -- per edge `e`, the bad set is the (≤2) roots of the two affine functions
  set root1 : LineSegment → Option ℚ := fun e =>
    if h : cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub e.p2 e.p1) ≠ 0 then
      some (-(cross (vsub q p) (vsub e.p2 e.p1))/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub e.p2 e.p1)))
    else none with hr1
  set root2 : LineSegment → Option ℚ := fun e =>
    if h : cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub e.p2 e.p1) ≠ 0 then
      some ((cross (vsub q p) (vsub e.p2 e.p1))/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub e.p2 e.p1)))
    else none with hr2
  set B : Finset ℚ := (poly.segments.filterMap root1).toFinset
    ∪ (poly.segments.filterMap root2).toFinset with hB
  refine ⟨B, ?_⟩
  intro k hk
  constructor <;> intro e he <;> simp only [transversalTo] at *
  · -- leg1 transversal
    rw [cross_leg1_eq]
    set d := vsub e.p2 e.p1 with hd_def
    have hdne : d ≠ ⟨0,0⟩ := by
      have := hnd e he; rw [hd_def]; intro h
      apply this
      have hx : e.p2.x - e.p1.x = 0 := congrArg Vector2D.x h
      have hy : e.p2.y - e.p1.y = 0 := congrArg Vector2D.y h
      simp only [vsub_x, vsub_y] at hx hy
      exact (Vector2D.ext (by linarith) (by linarith)).symm
    by_cases hβ : cross ⟨q.y-p.y, -(q.x-p.x)⟩ d = 0
    · -- then parallel-term nonzero
      have hα : cross (vsub q p) d ≠ 0 := by
        intro hα0; exact (not_both_cross_zero hpq hdne hα0) hβ
      rw [hβ, mul_zero, add_zero]; intro h; exact hα (by linarith [h])
    · intro hc
      have hkroot : k = -(cross (vsub q p) d)/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ d) := by
        field_simp at hc ⊢; linarith [hc]
      apply hk
      rw [hB, Finset.mem_union]; left
      rw [List.mem_toFinset, List.mem_filterMap]
      refine ⟨e, he, ?_⟩
      show root1 e = some k
      rw [hr1]; simp only
      rw [dif_pos (show cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub e.p2 e.p1) ≠ 0 from hβ), hkroot]
  · -- leg2 transversal
    rw [cross_leg2_eq]
    set d := vsub e.p2 e.p1 with hd_def
    have hdne : d ≠ ⟨0,0⟩ := by
      have := hnd e he; rw [hd_def]; intro h
      apply this
      have hx : e.p2.x - e.p1.x = 0 := congrArg Vector2D.x h
      have hy : e.p2.y - e.p1.y = 0 := congrArg Vector2D.y h
      simp only [vsub_x, vsub_y] at hx hy
      exact (Vector2D.ext (by linarith) (by linarith)).symm
    by_cases hβ : cross ⟨q.y-p.y, -(q.x-p.x)⟩ d = 0
    · have hα : cross (vsub q p) d ≠ 0 := by
        intro hα0; exact (not_both_cross_zero hpq hdne hα0) hβ
      rw [hβ, mul_zero, sub_zero]; intro h; exact hα (by linarith [h])
    · intro hc
      have hkroot : k = (cross (vsub q p) d)/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ d) := by
        field_simp at hc ⊢; linarith [hc]
      apply hk
      rw [hB, Finset.mem_union]; right
      rw [List.mem_toFinset, List.mem_filterMap]
      refine ⟨e, he, ?_⟩
      show root2 e = some k
      rw [hr2]; simp only
      rw [dif_pos (show cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub e.p2 e.p1) ≠ 0 from hβ), hkroot]

/-! ## The core one-sided constancy lemma -/

/-- **Core lemma.** Let `[A,B]` be a (transversal-to-both) segment avoiding every `Mlist`-edge
and avoiding `∂poly1 ∩ ∂poly2`, with `A ∈ poly1.interior ∩ poly2.interior`. Then `[A,B]`
misses both boundaries entirely, hence `B ∈ poly1.interior ∩ poly2.interior` too. -/
lemma good_leg_const (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {A B : Vector2D}
    (htr1 : transversalTo A B poly1) (htr2 : transversalTo A B poly2)
    (hM : ∀ e ∈ Mlist poly1 poly2, ∀ x ∈ (LineSegment.mk A B).toSet,
        x ∉ (LineSegment.mk e.1 e.2).toSet)
    (hAB12 : ∀ x ∈ (LineSegment.mk A B).toSet,
        ¬ (x ∈ poly1.toBoundarySet ∧ x ∈ poly2.toBoundarySet))
    (hA1 : A ∈ poly1.interior) (hA2 : A ∈ poly2.interior) :
    (∀ x ∈ (LineSegment.mk A B).toSet, x ∉ poly1.toBoundarySet)
      ∧ (∀ x ∈ (LineSegment.mk A B).toSet, x ∉ poly2.toBoundarySet) := by
  -- A is off both boundaries
  have hAoff1 : A ∉ poly1.toBoundarySet := fun hb => boundary_not_interior hb hA1
  have hAoff2 : A ∉ poly2.toBoundarySet := fun hb => boundary_not_interior hb hA2
  -- It suffices that bdyParams is empty: then [A,B] is boundary-free.
  -- We show bdyParams = ∅ by contradiction using the minimum crossing.
  have hfinB := bdyParams_finite htr1 htr2
  by_contra hcon
  -- so [A,B] meets a boundary somewhere; produce a bdyParam.
  have hne : (bdyParams A B poly1 poly2).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hcon
    -- every point on [A,B] is boundary-free
    constructor <;>
    · intro x hx
      obtain ⟨w, hw0, hw1, hxw⟩ := mem_seg_segPt hx
      rcases eq_or_lt_of_le hw0 with hw0eq | hw0lt
      · have : x = A := by rw [hxw, ← hw0eq]; exact segPt_zero A B
        rw [this]; first | exact hAoff1 | exact hAoff2
      · intro hb
        have : w ∈ bdyParams A B poly1 poly2 := by
          refine ⟨hw0lt, hw1, ?_⟩
          rw [hxw] at hb
          first | exact Or.inl hb | exact Or.inr hb
        rw [hempty] at this; exact this
  -- minimum crossing parameter
  set S := hfinB.toFinset with hS
  have hSne : S.Nonempty := by
    rw [hS, Set.Finite.toFinset_nonempty]; exact hne
  set tmin := S.min' hSne with htmin
  have htmin_mem : tmin ∈ bdyParams A B poly1 poly2 := by
    have hmem : tmin ∈ S := S.min'_mem hSne
    rw [hS] at hmem
    exact (Set.Finite.mem_toFinset hfinB).mp hmem
  obtain ⟨htmin0, htmin1, htminb⟩ := htmin_mem
  -- nothing strictly below tmin in (0,1] is a boundary param
  have hbelow : ∀ w, 0 < w → w < tmin → segPt A B w ∉ poly1.toBoundarySet ∧
      segPt A B w ∉ poly2.toBoundarySet := by
    intro w hw0 hwlt
    constructor <;>
    · intro hb
      have hwmem : w ∈ bdyParams A B poly1 poly2 :=
        ⟨hw0, le_of_lt (lt_of_lt_of_le hwlt htmin1), by first | exact Or.inl hb | exact Or.inr hb⟩
      have : tmin ≤ w := by
        rw [htmin]; apply S.min'_le
        rw [hS]; exact (Set.Finite.mem_toFinset hfinB).mpr hwmem
      linarith
  set c := segPt A B tmin with hc
  -- c is on [A,B]
  have hc_mem_AB : c ∈ (LineSegment.mk A B).toSet := segPt_mem_seg (le_of_lt htmin0) htmin1
  -- the midpoint c' = tmin/2
  set c' := tmin / 2 with hc'
  have hc'0 : 0 < c' := by rw [hc']; linarith
  have hc'lt : c' < tmin := by rw [hc']; linarith
  have hc'1 : c' ≤ 1 := le_of_lt (lt_of_lt_of_le hc'lt htmin1)
  -- prefix [A, segPt A B c'] is boundary-free, so segPt A B c' ∈ int poly1 ∩ int poly2
  have hpref := prefix_boundary_free (le_of_lt hc'0) hAoff1 hAoff2
    (fun w hw0 hwc' => hbelow w hw0 (lt_of_le_of_lt hwc' hc'lt))
  have hc'1int : segPt A B c' ∈ poly1.interior := by
    rw [← even_odd_constancy h1n h1e (P := A) (Q := segPt A B c') hpref.1]; exact hA1
  have hc'2int : segPt A B c' ∈ poly2.interior := by
    rw [← even_odd_constancy h2n h2e (P := A) (Q := segPt A B c') hpref.2]; exact hA2
  -- c ∈ ∂poly1 ∪ ∂poly2; not both.
  have hcnotboth : ¬ (c ∈ poly1.toBoundarySet ∧ c ∈ poly2.toBoundarySet) :=
    hAB12 c hc_mem_AB
  -- segment [segPt A B c', c] points = segPt A B w, w ∈ [c', tmin]
  have hseg_pts : ∀ x ∈ (LineSegment.mk (segPt A B c') c).toSet,
      ∃ w, c' ≤ w ∧ w ≤ tmin ∧ x = segPt A B w := by
    intro x hx
    obtain ⟨u, hu0, hu1, hxx, hxy⟩ := hx
    refine ⟨(1 - u) * c' + u * tmin, ?_, ?_, ?_⟩
    · nlinarith [hu0, hu1, le_of_lt hc'lt]
    · nlinarith [hu0, hu1, le_of_lt hc'lt]
    · ext
      · rw [hxx]; simp only [hc, segPt_x]; ring
      · rw [hxy]; simp only [hc, segPt_y]; ring
  rcases not_and_or.mp hcnotboth with hcn1 | hcn2
  · -- c ∉ poly1.boundary. Then since c ∈ ∂poly1∪∂poly2, c ∈ poly2.boundary.
    have hc_b2 : c ∈ poly2.toBoundarySet := by
      rcases htminb with h | h
      · rw [hc] at hcn1; exact absurd h hcn1
      · rw [hc]; exact h
    -- [c', c] is poly1-boundary-free, so c ∈ int poly1.
    have hbf1 : ∀ x ∈ (LineSegment.mk (segPt A B c') c).toSet, x ∉ poly1.toBoundarySet := by
      intro x hx hb
      obtain ⟨w, hcw, hwt, hxw⟩ := hseg_pts x hx
      rcases eq_or_lt_of_le hwt with hweq | hwlt
      · rw [hxw, hweq] at hb; rw [hc] at hcn1; exact hcn1 hb
      · exact (hbelow w (lt_of_lt_of_le hc'0 hcw) hwlt).1 (hxw ▸ hb)
    have hc_int1 : c ∈ poly1.interior := by
      rw [← even_odd_constancy h1n h1e (P := segPt A B c') (Q := c) hbf1]; exact hc'1int
    -- corner: c ∈ ∂poly2 ∩ int poly1 ⇒ on an M-edge
    obtain ⟨e, he, hce⟩ := Mlist_mem_of_inside' poly1 poly2 h1n h2n h1e h2e hfin hc_b2 hc_int1
    exact hM e he c hc_mem_AB hce
  · -- c ∉ poly2.boundary. Symmetric: c ∈ poly1.boundary, c ∈ int poly2.
    have hc_b1 : c ∈ poly1.toBoundarySet := by
      rcases htminb with h | h
      · rw [hc]; exact h
      · rw [hc] at hcn2; exact absurd h hcn2
    have hbf2 : ∀ x ∈ (LineSegment.mk (segPt A B c') c).toSet, x ∉ poly2.toBoundarySet := by
      intro x hx hb
      obtain ⟨w, hcw, hwt, hxw⟩ := hseg_pts x hx
      rcases eq_or_lt_of_le hwt with hweq | hwlt
      · rw [hxw, hweq] at hb; rw [hc] at hcn2; exact hcn2 hb
      · exact (hbelow w (lt_of_lt_of_le hc'0 hcw) hwlt).2 (hxw ▸ hb)
    have hc_int2 : c ∈ poly2.interior := by
      rw [← even_odd_constancy h2n h2e (P := segPt A B c') (Q := c) hbf2]; exact hc'2int
    obtain ⟨e, he, hce⟩ := Mlist_mem_of_inside poly1 poly2 h1n h2n h1e h2e hfin hc_b1 hc_int2
    exact hM e he c hc_mem_AB hce

/-! ## Genericity: legs avoiding a fixed list of (nondegenerate) segments -/

/-- If `[p,q]` avoids every segment in a list `L` of nondegenerate segments, then for small
generic `k` the leg `[p, Rrat p q k]` avoids every segment in `L`. -/
lemma leg1_avoid_list (p q : Vector2D) (hpq : p ≠ q) (L : List (Vector2D × Vector2D))
    (hLnd : ∀ e ∈ L, e.1 ≠ e.2)
    (hdisj : ∀ e ∈ L, ∀ x ∈ (LineSegment.mk p q).toSet, x ∉ (LineSegment.mk e.1 e.2).toSet) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ e ∈ L, ∀ x ∈ (LineSegment.mk p (Rrat p q k)).toSet,
        x ∉ (LineSegment.mk e.1 e.2).toSet := by
  have hedge : ∀ e ∈ L, ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ x ∈ (LineSegment.mk p (Rrat p q k)).toSet, x ∉ (LineSegment.mk e.1 e.2).toSet := by
    intro e he
    exact leg_bf_of_close p q e.1 e.2 hpq (hLnd e he)
      (fun x hx => hdisj e he x hx)
      (fun k s => segR (vR p) (Rk (vR p) (vR q) k) s)
      (fun k hk s hs => by
        obtain ⟨s', hs', hd⟩ := leg1_close (vR p) (vR q) k hk s hs
        rw [perp_norm_eq] at hd; exact ⟨s', hs', hd⟩)
      (fun k => LineSegment.mk p (Rrat p q k))
      (fun k x hx => by
        obtain ⟨t, ht, hxt⟩ := vR_mem_seg hx
        exact ⟨t, ht, by rw [hxt, vR_Rrat]⟩)
  obtain ⟨ε, hε, hgood⟩ := exists_uniform_eps L
    (fun e ε => ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ x ∈ (LineSegment.mk p (Rrat p q k)).toSet, x ∉ (LineSegment.mk e.1 e.2).toSet)
    (fun e ε ε' hε' hle hg k hk0 hkε x hx => hg k hk0 (le_trans hkε hle) x hx)
    hedge
  exact ⟨ε, hε, fun k hk0 hkε e he x hx => hgood e he k hk0 hkε x hx⟩

/-- Same for the second leg `[Rrat p q k, q]`. -/
lemma leg2_avoid_list (p q : Vector2D) (hpq : p ≠ q) (L : List (Vector2D × Vector2D))
    (hLnd : ∀ e ∈ L, e.1 ≠ e.2)
    (hdisj : ∀ e ∈ L, ∀ x ∈ (LineSegment.mk p q).toSet, x ∉ (LineSegment.mk e.1 e.2).toSet) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ e ∈ L, ∀ x ∈ (LineSegment.mk (Rrat p q k) q).toSet,
        x ∉ (LineSegment.mk e.1 e.2).toSet := by
  have hedge : ∀ e ∈ L, ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ x ∈ (LineSegment.mk (Rrat p q k) q).toSet, x ∉ (LineSegment.mk e.1 e.2).toSet := by
    intro e he
    exact leg_bf_of_close p q e.1 e.2 hpq (hLnd e he)
      (fun x hx => hdisj e he x hx)
      (fun k s => segR (Rk (vR p) (vR q) k) (vR q) s)
      (fun k hk s hs => by
        obtain ⟨s', hs', hd⟩ := leg2_close (vR p) (vR q) k hk s hs
        rw [perp_norm_eq] at hd; exact ⟨s', hs', hd⟩)
      (fun k => LineSegment.mk (Rrat p q k) q)
      (fun k x hx => by
        obtain ⟨t, ht, hxt⟩ := vR_mem_seg hx
        exact ⟨t, ht, by rw [hxt, vR_Rrat]⟩)
  obtain ⟨ε, hε, hgood⟩ := exists_uniform_eps L
    (fun e ε => ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ x ∈ (LineSegment.mk (Rrat p q k) q).toSet, x ∉ (LineSegment.mk e.1 e.2).toSet)
    (fun e ε ε' hε' hle hg k hk0 hkε x hx => hg k hk0 (le_trans hkε hle) x hx)
    hedge
  exact ⟨ε, hε, fun k hk0 hkε e he x hx => hgood e he k hk0 hkε x hx⟩

/-! ## Genericity: legs avoiding a fixed finite set of points -/

/-- A point `f ≠ p` collinear with the leg `[p, Rrat p q k]` has `cross (Rrat-p) (f-p) = 0`. -/
lemma point_on_leg1_cross {p q f : Vector2D} {k : ℚ}
    (hf : f ∈ (LineSegment.mk p (Rrat p q k)).toSet) :
    cross (vsub (Rrat p q k) p) (vsub f p) = 0 := by
  obtain ⟨t, _, _, hx, hy⟩ := hf
  simp only [cross_def, vsub_x, vsub_y, hx, hy]; ring

lemma point_on_leg2_cross {p q f : Vector2D} {k : ℚ}
    (hf : f ∈ (LineSegment.mk (Rrat p q k) q).toSet) :
    cross (vsub q (Rrat p q k)) (vsub f (Rrat p q k)) = 0 := by
  obtain ⟨t, _, _, hx, hy⟩ := hf
  simp only [cross_def, vsub_x, vsub_y, hx, hy]
  unfold Rrat; simp only; ring

/-- There is a finite bad set of `k` outside which both legs avoid every point of `pts`
(given each point is distinct from `p` and `q`). -/
lemma exists_avoid_pts_bad_k (p q : Vector2D) (hpq : p ≠ q) (pts : List Vector2D)
    (hpp : ∀ f ∈ pts, f ≠ p) (hpq' : ∀ f ∈ pts, f ≠ q) :
    ∃ B : Finset ℚ, ∀ k : ℚ, k ∉ B →
      (∀ f ∈ pts, f ∉ (LineSegment.mk p (Rrat p q k)).toSet) ∧
      (∀ f ∈ pts, f ∉ (LineSegment.mk (Rrat p q k) q).toSet) := by
  -- bad k where leg1/leg2 directions become parallel to (f - p) resp (f - q)
  set root1 : Vector2D → Option ℚ := fun f =>
    if h : cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f p) ≠ 0 then
      some (-(cross (vsub q p) (vsub f p))/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f p)))
    else none with hr1
  set root2 : Vector2D → Option ℚ := fun f =>
    if h : cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f q) ≠ 0 then
      some ((cross (vsub q p) (vsub f q))/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f q)))
    else none with hr2
  set B : Finset ℚ := (pts.filterMap root1).toFinset ∪ (pts.filterMap root2).toFinset with hB
  refine ⟨B, ?_⟩
  intro k hk
  constructor <;> intro f hf hmem
  · -- leg1: cross (Rrat-p)(f-p) = 0, but generically ≠ 0.
    have hfp : f ≠ p := hpp f hf
    have hfpne : vsub f p ≠ ⟨0,0⟩ := by
      intro h; apply hfp
      have hx : f.x - p.x = 0 := congrArg Vector2D.x h
      have hy : f.y - p.y = 0 := congrArg Vector2D.y h
      simp only [vsub_x, vsub_y] at hx hy; ext <;> linarith
    have hc := point_on_leg1_cross hmem
    rw [cross_leg1_eq] at hc
    set d := vsub f p with hd_def
    by_cases hβ : cross ⟨q.y-p.y, -(q.x-p.x)⟩ d = 0
    · have hα : cross (vsub q p) d ≠ 0 := fun hα0 => (not_both_cross_zero hpq hfpne hα0) hβ
      rw [hβ, mul_zero, add_zero] at hc; exact hα (by linarith [hc])
    · have hkroot : k = -(cross (vsub q p) d)/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ d) := by
        field_simp at hc ⊢; linarith [hc]
      apply hk
      rw [hB, Finset.mem_union]; left
      rw [List.mem_toFinset, List.mem_filterMap]
      refine ⟨f, hf, ?_⟩
      show root1 f = some k
      rw [hr1]; simp only
      rw [dif_pos (show cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f p) ≠ 0 from hβ), hkroot]
  · -- leg2: cross (q-Rrat)(f-Rrat) = 0.
    have hfq : f ≠ q := hpq' f hf
    have hfqne : vsub f q ≠ ⟨0,0⟩ := by
      intro h; apply hfq
      have hx : f.x - q.x = 0 := congrArg Vector2D.x h
      have hy : f.y - q.y = 0 := congrArg Vector2D.y h
      simp only [vsub_x, vsub_y] at hx hy; ext <;> linarith
    have hc := point_on_leg2_cross hmem
    -- cross (q - Rrat) (f - Rrat) : reduce to affine in k using d2 = f - q
    -- cross (q - Rrat) (f - Rrat) = cross_leg2-style with the point f relative to q.
    -- We expand directly.
    have hc2 : (cross (vsub q p) (vsub f q))/2 - k * (cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f q)) = 0 := by
      have : cross (vsub q (Rrat p q k)) (vsub f (Rrat p q k))
          = (cross (vsub q p) (vsub f q))/2 - k * (cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f q)) := by
        unfold Rrat vsub cross; simp; ring
      rw [this] at hc; exact hc
    set d := vsub f q with hd_def
    by_cases hβ : cross ⟨q.y-p.y, -(q.x-p.x)⟩ d = 0
    · -- not both zero: need cross(q-p, f-q) ≠ 0. Use not_both_cross_zero with d = f - q.
      have hα : cross (vsub q p) d ≠ 0 := fun hα0 => (not_both_cross_zero hpq hfqne hα0) hβ
      rw [hβ, mul_zero, sub_zero] at hc2; exact hα (by linarith [hc2])
    · have hkroot : k = (cross (vsub q p) d)/2 / (cross ⟨q.y-p.y, -(q.x-p.x)⟩ d) := by
        field_simp at hc2 ⊢; linarith [hc2]
      apply hk
      rw [hB, Finset.mem_union]; right
      rw [List.mem_toFinset, List.mem_filterMap]
      refine ⟨f, hf, ?_⟩
      show root2 f = some k
      rw [hr2]; simp only
      rw [dif_pos (show cross ⟨q.y-p.y, -(q.x-p.x)⟩ (vsub f q) ≠ 0 from hβ), hkroot]

/-! ## Assembly of the one-directional constancy -/

/-- A leg is good (transversal, M-free, F-free) provided `k` is generic and small. Packaged for
both legs. -/
lemma main_dir (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p q : Vector2D}
    (hpq : ∀ x ∈ (LineSegment.mk p q).toSet, ∀ e ∈ Mlist poly1 poly2,
        x ∉ (LineSegment.mk e.1 e.2).toSet)
    (hqF : q ∉ poly1.toBoundarySet ∩ poly2.toBoundarySet)
    (hp1 : p ∈ poly1.interior) (hp2 : p ∈ poly2.interior) :
    q ∈ poly1.interior ∧ q ∈ poly2.interior := by
  rcases eq_or_ne p q with hpqeq | hpne
  · subst hpqeq; exact ⟨hp1, hp2⟩
  -- p off both boundaries
  have hpoff1 : p ∉ poly1.toBoundarySet := fun hb => boundary_not_interior hb hp1
  have hpoff2 : p ∉ poly2.toBoundarySet := fun hb => boundary_not_interior hb hp2
  -- the F-points list
  set Flist : List Vector2D := hfin.toFinset.toList with hFlist
  have hFmem : ∀ f, f ∈ Flist ↔ f ∈ poly1.toBoundarySet ∩ poly2.toBoundarySet := by
    intro f; rw [hFlist, Finset.mem_toList, Set.Finite.mem_toFinset]
  have hFp : ∀ f ∈ Flist, f ≠ p := by
    intro f hf hfp; rw [hfp] at hf
    exact hpoff1 ((hFmem p).mp hf).1
  have hFq : ∀ f ∈ Flist, f ≠ q := by
    intro f hf hfq; rw [hfq] at hf
    exact hqF ((hFmem q).mp hf)
  -- reorder hpq into list-disjointness form for Mlist
  have hMdisj : ∀ e ∈ Mlist poly1 poly2, ∀ x ∈ (LineSegment.mk p q).toSet,
      x ∉ (LineSegment.mk e.1 e.2).toSet := fun e he x hx => hpq x hx e he
  -- genericity sets
  obtain ⟨Bt1, hBt1⟩ := exists_transversal_bad_k p q hpne poly1 h1n
  obtain ⟨Bt2, hBt2⟩ := exists_transversal_bad_k p q hpne poly2 h2n
  obtain ⟨Bp, hBp⟩ := exists_avoid_pts_bad_k p q hpne Flist hFp hFq
  obtain ⟨εM1, hεM1, hM1⟩ := leg1_avoid_list p q hpne (Mlist poly1 poly2)
    (Mlist_nondeg poly1 poly2) hMdisj
  obtain ⟨εM2, hεM2, hM2⟩ := leg2_avoid_list p q hpne (Mlist poly1 poly2)
    (Mlist_nondeg poly1 poly2) hMdisj
  -- choose k
  set ε := min εM1 εM2 with hε
  have hεpos : 0 < ε := lt_min hεM1 hεM2
  set Bad : Finset ℚ := Bt1 ∪ Bt2 ∪ Bp with hBad
  obtain ⟨k, hk⟩ : ∃ k : ℚ, k ∈ (Set.Ioo (0:ℚ) ε) \ (Bad : Set ℚ) :=
    ((Set.Ioo_infinite hεpos).diff Bad.finite_toSet).nonempty
  obtain ⟨⟨hk0, hkε⟩, hkBad⟩ := hk
  have hkBad' : k ∉ Bad := by simpa using hkBad
  have hkt1 : k ∉ Bt1 := fun h => hkBad' (by rw [hBad]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hkt2 : k ∉ Bt2 := fun h => hkBad' (by rw [hBad]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hkp : k ∉ Bp := fun h => hkBad' (by rw [hBad]; exact Finset.mem_union_right _ h)
  have hkεM1 : k ≤ εM1 := le_of_lt (lt_of_lt_of_le hkε (min_le_left _ _))
  have hkεM2 : k ≤ εM2 := le_of_lt (lt_of_lt_of_le hkε (min_le_right _ _))
  set R := Rrat p q k with hR
  -- transversality of legs
  obtain ⟨htr1_pR, htr1_Rq⟩ := hBt1 k hkt1
  obtain ⟨htr2_pR, htr2_Rq⟩ := hBt2 k hkt2
  -- point avoidance
  obtain ⟨hpt1, hpt2⟩ := hBp k hkp
  -- hAB12 for leg1 [p,R]
  have hAB12_pR : ∀ x ∈ (LineSegment.mk p R).toSet,
      ¬ (x ∈ poly1.toBoundarySet ∧ x ∈ poly2.toBoundarySet) := by
    intro x hx ⟨hb1, hb2⟩
    have hxF : x ∈ Flist := (hFmem x).mpr ⟨hb1, hb2⟩
    exact hpt1 x hxF hx
  have hAB12_Rq : ∀ x ∈ (LineSegment.mk R q).toSet,
      ¬ (x ∈ poly1.toBoundarySet ∧ x ∈ poly2.toBoundarySet) := by
    intro x hx ⟨hb1, hb2⟩
    have hxF : x ∈ Flist := (hFmem x).mpr ⟨hb1, hb2⟩
    exact hpt2 x hxF hx
  -- M-freeness for legs
  have hM_pR : ∀ e ∈ Mlist poly1 poly2, ∀ x ∈ (LineSegment.mk p R).toSet,
      x ∉ (LineSegment.mk e.1 e.2).toSet := fun e he x hx => hM1 k hk0 hkεM1 e he x hx
  have hM_Rq : ∀ e ∈ Mlist poly1 poly2, ∀ x ∈ (LineSegment.mk R q).toSet,
      x ∉ (LineSegment.mk e.1 e.2).toSet := fun e he x hx => hM2 k hk0 hkεM2 e he x hx
  -- leg1: [p,R] boundary-free; R ∈ int
  obtain ⟨hbf1_pR, hbf2_pR⟩ := good_leg_const poly1 poly2 h1n h2n h1e h2e hfin
    htr1_pR htr2_pR hM_pR hAB12_pR hp1 hp2
  have hR1 : R ∈ poly1.interior := by
    rw [← even_odd_constancy h1n h1e (P := p) (Q := R) hbf1_pR]; exact hp1
  have hR2 : R ∈ poly2.interior := by
    rw [← even_odd_constancy h2n h2e (P := p) (Q := R) hbf2_pR]; exact hp2
  -- leg2: [R,q] boundary-free; q ∈ int
  obtain ⟨hbf1_Rq, hbf2_Rq⟩ := good_leg_const poly1 poly2 h1n h2n h1e h2e hfin
    htr1_Rq htr2_Rq hM_Rq hAB12_Rq hR1 hR2
  refine ⟨?_, ?_⟩
  · rw [← even_odd_constancy h1n h1e (P := R) (Q := q) hbf1_Rq]; exact hR1
  · rw [← even_odd_constancy h2n h2e (P := R) (Q := q) hbf2_Rq]; exact hR2

/-! ## The corner lemma: an endpoint reached through the interior is not a double-boundary point.

The genuinely hard step.  If `q ∈ ∂poly1 ∩ ∂poly2`, while a whole half-open segment `[R,q)`
(its open part) lies in `poly1.interior ∩ poly2.interior`, and `[R,q]` avoids the `Mlist`-edges,
we derive a contradiction by manufacturing a point `z` on the `poly1`-edge through `q`, close to
`q` and in `poly2.interior`; the kept clip-piece with `z` in its interior has `q` as an endpoint,
hence `q` lies on an `Mlist`-edge. -/

/-- A point on the line `[R,q]` (off `poly2`'s boundary, in `poly2.interior`) shifted
perpendicular lands, for the right shift, on the line of edge `[a₁,a₂]`. We capture the algebra:
`Psh R q v k` is on the line through `a₁,a₂` exactly when `k` solves a linear equation. -/
lemma Psh_on_edge_line (R q v a₁ a₂ : Vector2D) (k : ℚ)
    (hk : cross (vsub a₂ a₁) ⟨q.y - R.y, -(q.x - R.x)⟩ ≠ 0)
    (hkval : k = cross (vsub a₂ a₁) (vsub a₁ v) / cross (vsub a₂ a₁) ⟨q.y - R.y, -(q.x - R.x)⟩) :
    cross (vsub a₂ a₁) (vsub (Psh R q v k) a₁) = 0 := by
  -- vsub (Psh R q v k) a₁ = (v - a₁) + k·perp
  have hexp : cross (vsub a₂ a₁) (vsub (Psh R q v k) a₁)
      = cross (vsub a₂ a₁) (vsub v a₁) + k * cross (vsub a₂ a₁) ⟨q.y-R.y, -(q.x-R.x)⟩ := by
    unfold Psh vsub cross; simp; ring
  rw [hexp, hkval]
  field_simp
  unfold cross vsub; ring

/-- The perpendicular-shifted point of an interior point `v` (on the line `[R,q]`, off `poly2`'s
boundary) stays in `poly2.interior` for small `k`. -/
lemma Psh_mem_interior (R q v : Vector2D) (poly2 : Polygon)
    (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2) (h2e : poly2.segments ≠ [])
    (hvline : ∃ sv : ℝ, sv ∈ Set.Icc (0:ℝ) 1 ∧ vR v = segR (vR R) (vR q) sv)
    (hvoff : v ∉ poly2.toBoundarySet) (hvint : v ∈ poly2.interior) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε → Psh R q v k ∈ poly2.interior := by
  obtain ⟨ε, hε, hbf⟩ := legPt_bf R q v poly2 h2n hvline hvoff
  refine ⟨ε, hε, fun k hk0 hkε => ?_⟩
  rw [← even_odd_constancy h2n h2e (P := v) (Q := Psh R q v k)
    (fun x hx => hbf k hk0 hkε x hx)]
  exact hvint

-- The **corner lemma** `endpoint_off_double` and the constancy theorem `AcapB_const` are proved
-- in `Polygons2.CornerC` (which imports this file and reuses the helpers above, including
-- `main_dir`).  They are stated there to keep this file free of `sorry`.

/-- `Psh R q v k` lies on the segment `[a₁,a₂]` (given it's on the line and its param is in
`[0,1]`). We compute its parameter as a function of `k`. -/
lemma Psh_param_on_edge (R q v a₁ a₂ : Vector2D) (k : ℚ)
    (hline : cross (vsub a₂ a₁) (vsub (Psh R q v k) a₁) = 0)
    (hdx : a₂.x - a₁.x ≠ 0) (huv : ((Psh R q v k).x - a₁.x) / (a₂.x - a₁.x) ∈ Set.Icc (0:ℚ) 1) :
    Psh R q v k ∈ (LineSegment.mk a₁ a₂).toSet := by
  apply mem_seg_of_x
  · -- line condition rewritten as (a₂.x-a₁.x)(z.y-a₁.y) - (a₂.y-a₁.y)(z.x-a₁.x) = 0
    have := hline; simp only [cross_def, vsub_x, vsub_y] at this; linarith [this]
  · exact hdx
  · exact huv

end Polygons2
end
