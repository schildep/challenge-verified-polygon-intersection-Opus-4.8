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
import Polygons2.GoodRay
import Polygons2.Bridge
import Polygons2.Constancy
import Polygons2.Assemble
import Polygons2.Assemble2

/-!
# Final assembly: `intersection_polys_core`.

Pure assembly of the polygon-intersection construction from already-proven infrastructure.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- Build a forward ray from `p` (direction `⟨1,k⟩`) that misses every point of `V`
(each `≠ p`). -/
lemma build_ray (p : Vector2D) (V : List Vector2D) (hpV : ∀ w ∈ V, w ≠ p) :
    ∃ r : Ray, r.origin = p ∧ (∀ w ∈ V, w ∉ r.toSet) := by
  obtain ⟨k, _, hkV⟩ := exists_good_dir' p [] V (by simp) hpV
  have hd : (⟨1, k⟩ : Vector2D) ≠ ⟨0, 0⟩ := by intro h; simp [Vector2D.ext_iff] at h
  refine ⟨⟨p, ⟨1, k⟩, hd⟩, rfl, ?_⟩
  intro w hw hwr
  obtain ⟨t, ht0, htx, hty⟩ := hwr
  exact hkV w hw ⟨t, ht0, by simpa using htx, by simpa using hty⟩

/-- `rayAvoidsVertices` from a pointwise off-vertex fact. -/
lemma rayAvoidsVertices_of_off (r : Ray) (poly : Polygon)
    (h : ∀ w ∈ poly.vertices, w ∉ r.toSet) : rayAvoidsVertices r poly := by
  rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hwr, hwv⟩
  exact h w hwv hwr

/-- A point of the forward ray `p + t·d` (`t ≥ 0`) at parameter `t < τ` for the threshold `τ`. -/
lemma forward_threshold (p d a b : Vector2D) (hpar : cross d (vsub b a) ≠ 0) :
    ∃ τ : ℚ, 0 < τ ∧ ∀ t : ℚ, 0 < t → t < τ →
      (⟨p.x + t * d.x, p.y + t * d.y⟩ : Vector2D) ∉ (LineSegment.mk a b).toSet := by
  -- The unique parameter where p + t·d hits the line through a,b.
  have hcd : cross (vsub b a) d ≠ 0 := by
    rw [show cross (vsub b a) d = - cross d (vsub b a) by simp only [cross_def, vsub_x, vsub_y]; ring]
    exact neg_ne_zero.mpr hpar
  set tstar : ℚ := - cross (vsub b a) (vsub p a) / cross (vsub b a) d with htstar
  set τ : ℚ := if 0 < tstar then tstar else 1 with hτ
  have hτpos : 0 < τ := by
    rw [hτ]; split <;> [assumption; norm_num]
  refine ⟨τ, hτpos, ?_⟩
  intro t ht0' htτ hmem
  have ht0 : (0:ℚ) ≤ t := le_of_lt ht0'
  -- membership ⇒ collinear ⇒ t = tstar
  obtain ⟨u, hu0, hu1, hux, huy⟩ := hmem
  -- collinearity: cross (b-a) (q - a) = 0
  have hcol : cross (vsub b a) (vsub ⟨p.x + t*d.x, p.y + t*d.y⟩ a) = 0 := by
    simp only [cross_def, vsub_x, vsub_y] at *
    -- q.x = (1-u)a.x+u b.x, q.y = (1-u)a.y+u b.y
    rw [hux, huy]; ring
  -- expand: cross(b-a)(p-a) + t cross(b-a) d = 0
  have hexp : cross (vsub b a) (vsub p a) + t * cross (vsub b a) d = 0 := by
    have : cross (vsub b a) (vsub ⟨p.x + t*d.x, p.y + t*d.y⟩ a)
        = cross (vsub b a) (vsub p a) + t * cross (vsub b a) d := by
      simp only [cross_def, vsub_x, vsub_y]; ring
    rw [this] at hcol; linarith [hcol]
  have htt : t = tstar := by
    rw [htstar, eq_div_iff hcd]; linarith [hexp]
  -- contradiction with t < τ
  rw [hτ] at htτ
  split at htτ
  · -- τ = tstar > 0, t = tstar but t < tstar
    rw [htt] at htτ; exact absurd htτ (lt_irrefl _)
  · -- τ = 1, tstar ≤ 0, but t = tstar > 0 ⇒ contradiction
    rename_i hnpos
    rw [htt] at ht0'
    exact absurd ht0' hnpos

/-- Perturbation: a generic forward direction `d = ⟨1,c⟩` (non-parallel to every edge of `E`,
which each must be nondegenerate) and a positive `ε` such that every forward point
`p + t·d` for `0 < t ≤ ε` lies off every edge of `E` and differs from every point of `Pts`
(each distinct from `p`). -/
lemma exists_perturb (p : Vector2D) (E : List LineSegment) (Pts : List Vector2D)
    (hnd : ∀ e ∈ E, e.p1 ≠ e.p2) :
    ∃ (c ε : ℚ), 0 < ε ∧
      (∀ t : ℚ, 0 < t → t ≤ ε → (∀ e ∈ E,
        (⟨p.x + t * 1, p.y + t * c⟩ : Vector2D) ∉ e.toSet) ∧
        (∀ w ∈ Pts, (⟨p.x + t * 1, p.y + t * c⟩ : Vector2D) ≠ w)) := by
  -- Direction non-parallel to every edge direction, and ray misses all `Pts` distinct from `p`.
  obtain ⟨c, hcpar, hcV⟩ := exists_good_dir' p (E.map (fun e => vsub e.p2 e.p1))
    (Pts.filter (fun w => decide (w ≠ p)))
    (by
      intro d hd
      rw [List.mem_map] at hd
      obtain ⟨e, he, hde⟩ := hd
      intro h0; apply hnd e he
      rw [← hde] at h0
      have hx : e.p2.x - e.p1.x = 0 := by have := congrArg Vector2D.x h0; simpa [vsub] using this
      have hy : e.p2.y - e.p1.y = 0 := by have := congrArg Vector2D.y h0; simpa [vsub] using this
      apply (Vector2D.ext_iff).2; constructor <;> [linarith; linarith])
    (by
      intro w hw
      rw [List.mem_filter] at hw
      simpa using hw.2)
  set d : Vector2D := ⟨1, c⟩ with hd
  -- For each edge, a positive threshold below which p + t·d misses it.
  have hpar' : ∀ e ∈ E, cross d (vsub e.p2 e.p1) ≠ 0 := by
    intro e he
    have hc := hcpar (vsub e.p2 e.p1) (by rw [List.mem_map]; exact ⟨e, he, rfl⟩)
    -- hc : cross (vsub e.p2 e.p1) ⟨1,c⟩ ≠ 0;  goal cross ⟨1,c⟩ (vsub..) ≠ 0
    rw [hd]
    rw [show cross (⟨1,c⟩ : Vector2D) (vsub e.p2 e.p1) = - cross (vsub e.p2 e.p1) ⟨1,c⟩ by
      simp only [cross_def, vsub_x, vsub_y]; ring]
    exact neg_ne_zero.mpr hc
  -- Collect thresholds via exists_uniform_eps.
  obtain ⟨ε, hε, hgood⟩ := exists_uniform_eps E
    (fun e τ => ∀ t : ℚ, 0 < t → t < τ →
      (⟨p.x + t * 1, p.y + t * c⟩ : Vector2D) ∉ e.toSet)
    (fun e τ τ' hτ' hle hg t ht0 htτ => hg t ht0 (lt_of_lt_of_le htτ hle))
    (fun e he => by
      obtain ⟨τ, hτ, hτspec⟩ := forward_threshold p d e.p1 e.p2 (hpar' e he)
      refine ⟨τ, hτ, ?_⟩
      intro t ht0 htτ
      have := hτspec t ht0 htτ
      rw [hd] at this; exact this)
  refine ⟨c, ε / 2, by positivity, ?_⟩
  intro t ht0 htε
  refine ⟨fun e he => hgood e he t ht0 (by linarith [htε]), ?_⟩
  intro w hw hwq
  -- forward point equals w ⇒ w on ray ⇒ either w = p (impossible, t>0) or w filtered (avoided)
  by_cases hwp : w = p
  · have hx : p.x + t * 1 = w.x := congrArg Vector2D.x hwq
    rw [hwp] at hx
    have : t = 0 := by linarith [hx]
    linarith [ht0]
  · have hwf : w ∈ Pts.filter (fun w => decide (w ≠ p)) := by
      rw [List.mem_filter]; exact ⟨hw, by simpa using hwp⟩
    exact hcV w hwf ⟨t, le_of_lt ht0, by rw [← hwq], by rw [← hwq]⟩

theorem intersection_polys_core (poly1 poly2 : Polygon) (M : List (Vector2D × Vector2D))
    (polys : List Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (h_fin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    (hMsub : ∀ e ∈ M, ∀ x ∈ (LineSegment.mk e.1 e.2).toSet,
        x ∈ poly1.toBoundarySet ∨ x ∈ poly2.toBoundarySet)
    (hMcount : ∀ r : Ray, rayAvoidsVertices r poly1 → rayAvoidsVertices r poly2 →
        (∀ x ∈ r.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False) →
        M.countP (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩)) = insideCrossings r poly1 poly2)
    (hMin1 : ∀ p : Vector2D, p ∈ poly1.toBoundarySet → p ∈ poly2.interior →
        ∃ e ∈ M, p ∈ (LineSegment.mk e.1 e.2).toSet)
    (hMin2 : ∀ p : Vector2D, p ∈ poly2.toBoundarySet → p ∈ poly1.interior →
        ∃ e ∈ M, p ∈ (LineSegment.mk e.1 e.2).toSet)
    (hAcapB_const : ∀ {a b : Vector2D},
        (∀ x ∈ (LineSegment.mk a b).toSet, ∀ e ∈ M, x ∉ (LineSegment.mk e.1 e.2).toSet) →
        (a ∈ poly1.interior ∩ poly2.interior ↔ b ∈ poly1.interior ∩ poly2.interior))
    (h_nd : ∀ Q ∈ polys, ∀ s ∈ Q.segments, s.p1 ≠ s.p2)
    (h_cross : ∀ r : Ray, (polys.map (fun Q => Q.segments)).flatten.countP
        (fun s => decide (rayIntersectsSegment r s))
          = M.countP (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩)))
    (h_segc : ∀ Q ∈ polys, ∀ s ∈ Q.segments, ∃ e ∈ M, s.toSet = (LineSegment.mk e.1 e.2).toSet)
    (h_cover : ∀ e ∈ M, ∃ Q ∈ polys, ∃ s ∈ Q.segments, s.toSet = (LineSegment.mk e.1 e.2).toSet) :
    ∃ polys' : List Polygon,
      (∀ Q ∈ polys', ∀ seg ∈ Q.segments, seg.p1 ≠ seg.p2) ∧
      (∀ p : Vector2D, (∃ Q ∈ polys', p ∈ Q.toBoundarySet) →
          p ∈ poly1.toBoundarySet ∨ p ∈ poly2.toBoundarySet) ∧
      (∀ p : Vector2D, (∀ Q ∈ polys', ∀ seg ∈ Q.segments, p ∉ seg.toSet) →
          ∃ r : Ray, r.origin = p ∧ (∀ Q ∈ polys', rayAvoidsVertices r Q) ∧
            (((polys'.map (fun Q => Q.segments)).flatten.countP
                (fun seg => decide (rayIntersectsSegment r seg))) % 2 = 1 ↔
              p ∈ poly1.interior ∩ poly2.interior)) := by
  set polys' : List Polygon := polys.filter (fun Q => decide (2 ≤ Q.vertices.length)) with hpolys'
  have hmem' : ∀ Q ∈ polys', Q ∈ polys ∧ 2 ≤ Q.vertices.length := by
    intro Q hQ
    rw [hpolys', List.mem_filter] at hQ
    exact ⟨hQ.1, by simpa using hQ.2⟩
  have hsub' : ∀ Q ∈ polys', Q ∈ polys := fun Q hQ => (hmem' Q hQ).1
  have hlen' : ∀ Q ∈ polys', 2 ≤ Q.vertices.length := fun Q hQ => (hmem' Q hQ).2
  have hne' : ∀ Q ∈ polys', Q.segments ≠ [] :=
    fun Q hQ => (segments_ne_nil_iff Q).2 (hlen' Q hQ)
  have hcover' : ∀ e ∈ M, ∃ Q ∈ polys', ∃ s ∈ Q.segments, s.toSet = (LineSegment.mk e.1 e.2).toSet := by
    intro e he
    obtain ⟨Q, hQ, s, hs, hst⟩ := h_cover e he
    have hQ2 : 2 ≤ Q.vertices.length := (segments_ne_nil_iff Q).1 (by intro h; rw [h] at hs; simp at hs)
    refine ⟨Q, ?_, s, hs, hst⟩
    rw [hpolys', List.mem_filter]; exact ⟨hQ, by simpa using hQ2⟩
  have hnd' : ∀ Q ∈ polys', ∀ s ∈ Q.segments, s.p1 ≠ s.p2 :=
    fun Q hQ s hs => h_nd Q (hsub' Q hQ) s hs
  -- The combined count over polys' equals over polys (and hence the M-count).
  have hcomb : ∀ r : Ray, (polys'.map (fun Q => Q.segments)).flatten.countP
      (fun seg => decide (rayIntersectsSegment r seg))
      = M.countP (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩)) := by
    intro r
    rw [hpolys', filter_flatten_countP polys (fun seg => decide (rayIntersectsSegment r seg))]
    exact h_cross r
  refine ⟨polys', hnd', ?_, ?_⟩
  · -- Conjunct 2: boundary
    rintro p ⟨Q, hQ, hpQ⟩
    obtain ⟨s, hs, hps⟩ := hpQ
    obtain ⟨e, he, hse⟩ := h_segc Q (hsub' Q hQ) s hs
    exact hMsub e he p (hse ▸ hps)
  · -- Conjunct 3: parity
    intro p hpoff'
    have hpM : ∀ e ∈ M, p ∉ (LineSegment.mk e.1 e.2).toSet := by
      intro e he hpe
      obtain ⟨Q, hQ, s, hs, hst⟩ := hcover' e he
      exact hpoff' Q hQ s hs (hst ▸ hpe)
    set Slist : List Vector2D := h_fin.toFinset.toList with hSlist
    have hSlist_mem : ∀ x ∈ Slist, x ∈ poly1.toBoundarySet ∩ poly2.toBoundarySet := by
      intro x hx
      rw [hSlist, Finset.mem_toList, Set.Finite.mem_toFinset] at hx
      exact hx
    have hSlist_iff : ∀ x : Vector2D, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet →
        x ∈ Slist := by
      intro x h1 h2
      rw [hSlist, Finset.mem_toList, Set.Finite.mem_toFinset]
      exact ⟨h1, h2⟩
    set Vlist : List Vector2D := polys'.flatMap (fun Q => Q.vertices) with hVlist
    have hVlist_bd : ∀ v ∈ Vlist, ∃ Q ∈ polys', v ∈ Q.toBoundarySet := by
      intro v hv
      rw [hVlist, List.mem_flatMap] at hv
      obtain ⟨Q, hQ, hvQ⟩ := hv
      exact ⟨Q, hQ, vertex_on_boundary (hlen' Q hQ) hvQ⟩
    -- Anchor: for p' off both boundaries and off polys' segments.
    have anchor : ∀ p' : Vector2D, p' ∉ poly1.toBoundarySet → p' ∉ poly2.toBoundarySet →
        p' ∉ poly1.vertices → p' ∉ poly2.vertices →
        (∀ Q ∈ polys', ∀ s ∈ Q.segments, p' ∉ s.toSet) →
        (p' ∈ symmDiffAll (polys'.map Polygon.interior) ↔ p' ∈ poly1.interior ∩ poly2.interior) := by
      intro p' hp'1 hp'2 hp'v1 hp'v2 hp'off
      -- p' off all segments of poly1 and poly2.
      have hp'seg1 : ∀ s ∈ poly1.segments, p' ∉ s.toSet :=
        fun s hs hps => hp'1 ⟨s, hs, hps⟩
      have hp'seg2 : ∀ s ∈ poly2.segments, p' ∉ s.toSet :=
        fun s hs hps => hp'2 ⟨s, hs, hps⟩
      -- All vertices to avoid are ≠ p'.
      have hpV : ∀ w ∈ (Vlist ++ poly1.vertices ++ poly2.vertices ++ Slist), w ≠ p' := by
        intro w hw
        simp only [List.mem_append] at hw
        rcases hw with ((hw | hw) | hw) | hw
        · obtain ⟨Q, hQ, s, hs, hps⟩ := hVlist_bd w hw
          intro h; subst h; exact hp'off Q hQ s hs hps
        · intro he; subst he; exact hp'v1 hw
        · intro he; subst he; exact hp'v2 hw
        · intro he; subst he; exact hp'1 (hSlist_mem w hw).1
      obtain ⟨r', hr'o, hr'V⟩ := build_ray p' _ hpV
      have hav_all : ∀ w : Vector2D, (w ∈ Vlist ∨ w ∈ poly1.vertices ∨ w ∈ poly2.vertices ∨ w ∈ Slist)
          → w ∉ r'.toSet := by
        intro w hw
        apply hr'V
        simp only [List.mem_append]
        tauto
      -- rayAvoidsVertices for everyone
      have hav1 : rayAvoidsVertices r' poly1 :=
        rayAvoidsVertices_of_off r' poly1 (fun w hw => hav_all w (Or.inr (Or.inl hw)))
      have hav2 : rayAvoidsVertices r' poly2 :=
        rayAvoidsVertices_of_off r' poly2 (fun w hw => hav_all w (Or.inr (Or.inr (Or.inl hw))))
      have havQ : ∀ Q ∈ polys', rayAvoidsVertices r' Q := by
        intro Q hQ
        apply rayAvoidsVertices_of_off
        intro w hw
        apply hav_all w
        left; rw [hVlist, List.mem_flatMap]; exact ⟨Q, hQ, hw⟩
      -- hS': r' avoids ∂A∩∂B.
      have hS' : ∀ x ∈ r'.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False := by
        intro x hxr h1 h2
        have hxS : x ∈ Slist := hSlist_iff x h1 h2
        exact hav_all x (Or.inr (Or.inr (Or.inr hxS))) hxr
      -- Bridge: symmDiff ↔ combined count odd.
      have hbridge := symmDiffAll_interior_iff polys' p' r' hr'o hp'off hnd' havQ
      -- combined count = M-count (mod nothing; equal as naturals).
      have hMc : M.countP (fun e => decide (rayIntersectsSegment r' ⟨e.1, e.2⟩))
          = insideCrossings r' poly1 poly2 := hMcount r' hav1 hav2 hS'
      -- insideCrossings parity.
      have hpar := insideCrossings_parity poly1 poly2 r' h1n h2n hav1 hav2 hS'
      -- interior characterizations for poly1, poly2.
      have hint1 := mem_interior_iff poly1 p' r' hr'o hav1 h1n
      have hint2 := mem_interior_iff poly2 p' r' hr'o hav2 h2n
      -- Chain everything.
      rw [hbridge, hcomb r', hMc]
      constructor
      · intro hodd
        have hins : insideCrossings r' poly1 poly2 % 2 = 1 := hodd
        rw [hpar] at hins
        have hN1 : intersectionRayPolygonSegmentsNumber r' poly1 % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (intersectionRayPolygonSegmentsNumber r' poly1) with h | h
          · rw [h] at hins; simp at hins
          · exact h
        have hN2 : intersectionRayPolygonSegmentsNumber r' poly2 % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (intersectionRayPolygonSegmentsNumber r' poly2) with h | h
          · rw [h] at hins; simp at hins
          · exact h
        exact ⟨hint1.2 ⟨hp'seg1, hN1⟩, hint2.2 ⟨hp'seg2, hN2⟩⟩
      · rintro ⟨hi1, hi2⟩
        have hN1 := (hint1.1 hi1).2
        have hN2 := (hint2.1 hi2).2
        rw [hpar, hN1, hN2]
    -- End anchor.
    -- Non-emptiness of the two input polygons.  (The surrounding construction
    -- `exists_intersection_polys` supplies `poly1.vertices.length ≥ 2` and
    -- `poly2.vertices.length ≥ 2`; these are the corresponding `segments ≠ []` facts.)
    have poly1_seg_ne : poly1.segments ≠ [] := h1e
    have poly2_seg_ne : poly2.segments ≠ [] := h2e
    -- Build a ray from p avoiding polys' vertices (each ≠ p since on polys' boundary).
    have hpVp : ∀ w ∈ Vlist, w ≠ p := by
      intro w hw
      obtain ⟨Q, hQ, s, hs, hps⟩ := hVlist_bd w hw
      intro h; subst h; exact hpoff' Q hQ s hs hps
    obtain ⟨r, hro, hrV⟩ := build_ray p Vlist hpVp
    have havp : ∀ Q ∈ polys', rayAvoidsVertices r Q := by
      intro Q hQ
      apply rayAvoidsVertices_of_off
      intro w hw
      apply hrV
      rw [hVlist, List.mem_flatMap]; exact ⟨Q, hQ, hw⟩
    have hbridge_p := symmDiffAll_interior_iff polys' p r hro hpoff' hnd' havp
    -- The combined edge list of E for perturbation.
    set E : List LineSegment :=
      poly1.segments ++ poly2.segments ++ polys'.flatMap (fun Q => Q.segments) with hE
    have hE_nd : ∀ e ∈ E, e.p1 ≠ e.p2 := by
      intro e he
      rw [hE, List.mem_append, List.mem_append] at he
      rcases he with (he | he) | he
      · exact h1n e he
      · exact h2n e he
      · rw [List.mem_flatMap] at he; obtain ⟨Q, hQ, hsQ⟩ := he
        exact hnd' Q hQ e hsQ
    -- Helper: membership of a point of segment [p,p'] (p' = p+ε·d) as a forward point.
    -- The transfer equivalence.
    have htrans : p ∈ symmDiffAll (polys'.map Polygon.interior) ↔
        p ∈ poly1.interior ∩ poly2.interior := by
      by_cases hpA : p ∈ poly1.toBoundarySet
      · -- p ∈ ∂A ⇒ p ∉ poly1.interior ⇒ p ∉ A∩B; transfer A∩B-status via AcapB_const
        -- (works whether or not p ∈ ∂B, so no S-exclusion is needed).
        have hpni1 : p ∉ poly1.interior := boundary_not_interior hpA
        -- Perturb to p'.
        obtain ⟨c, ε, hε, hperb⟩ := exists_perturb p E (poly1.vertices ++ poly2.vertices) hE_nd
        set p' : Vector2D := ⟨p.x + ε * 1, p.y + ε * c⟩ with hp'def
        -- A point of [p,p'].toSet is p, or a forward point with 0 < t ≤ ε.
        have hseg_pt : ∀ x ∈ (LineSegment.mk p p').toSet, x = p ∨
            ∃ t : ℚ, 0 < t ∧ t ≤ ε ∧ x = ⟨p.x + t * 1, p.y + t * c⟩ := by
          intro x hx
          obtain ⟨u, hu0, hu1, hxx, hxy⟩ := hx
          by_cases hu : u = 0
          · left; apply Vector2D.ext
            · rw [hxx, hu]; ring
            · rw [hxy, hu]; ring
          · right
            have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
            refine ⟨u * ε, by positivity, by nlinarith [hu1, hε.le, hupos], ?_⟩
            apply Vector2D.ext
            · rw [hxx, hp'def]; ring
            · rw [hxy, hp'def]; ring
        -- p' = endpoint is off every edge of E and ≠ poly1/poly2 vertices.
        have hp'_offE : ∀ e ∈ E, p' ∉ e.toSet := by
          intro e he
          have := (hperb ε hε (le_refl ε)).1 e he
          rw [hp'def]; exact this
        have hp'_neV : ∀ w ∈ poly1.vertices ++ poly2.vertices, p' ≠ w := by
          intro w hw
          have := (hperb ε hε (le_refl ε)).2 w hw
          rw [hp'def]; exact this
        -- A point of [p,p'] off poly2 and polys' edges (p is off those; forward pts via hperb).
        have hleg_off : ∀ e ∈ E, p ∉ e.toSet → ∀ x ∈ (LineSegment.mk p p').toSet, x ∉ e.toSet := by
          intro e he hpe x hx
          rcases hseg_pt x hx with hxp | ⟨t, ht0, htε, hxt⟩
          · rw [hxp]; exact hpe
          · rw [hxt]; exact (hperb t ht0 htε).1 e he
        -- Membership helpers for E.
        have hmemE1 : ∀ s ∈ poly1.segments, s ∈ E := fun s hs => by
          rw [hE]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hs)))
        have hmemE2 : ∀ s ∈ poly2.segments, s ∈ E := fun s hs => by
          rw [hE]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hs)))
        have hmemEQ : ∀ Q ∈ polys', ∀ s ∈ Q.segments, s ∈ E := fun Q hQ s hs => by
          rw [hE]; refine List.mem_append.mpr (Or.inr ?_)
          rw [List.mem_flatMap]; exact ⟨Q, hQ, hs⟩
        have hp_offQ : ∀ Q ∈ polys', ∀ s ∈ Q.segments, p ∉ s.toSet := hpoff'
        -- p' off boundaries / segments.
        have hp'A : p' ∉ poly1.toBoundarySet := by
          rintro ⟨s, hs, hps⟩; exact hp'_offE s (hmemE1 s hs) hps
        have hp'B : p' ∉ poly2.toBoundarySet := by
          rintro ⟨s, hs, hps⟩; exact hp'_offE s (hmemE2 s hs) hps
        have hp'offQ : ∀ Q ∈ polys', ∀ s ∈ Q.segments, p' ∉ s.toSet :=
          fun Q hQ s hs => hp'_offE s (hmemEQ Q hQ s hs)
        have hp'v1 : p' ∉ poly1.vertices := fun hv =>
          hp'_neV p' (List.mem_append.mpr (Or.inl hv)) rfl
        have hp'v2 : p' ∉ poly2.vertices := fun hv =>
          hp'_neV p' (List.mem_append.mpr (Or.inr hv)) rfl
        -- [p,p'] avoids every M-edge: p does (hpM); forward points avoid ∂A∪∂B ⊇ M-edges.
        have hpp' : ∀ x ∈ (LineSegment.mk p p').toSet, ∀ e ∈ M,
            x ∉ (LineSegment.mk e.1 e.2).toSet := by
          intro x hx e he
          rcases hseg_pt x hx with hxp | ⟨t, ht0, htε, hxt⟩
          · rw [hxp]; exact hpM e he
          · intro hxe
            rcases hMsub e he x hxe with ⟨s, hs, hxs⟩ | ⟨s, hs, hxs⟩
            · exact (hperb t ht0 htε).1 s (hmemE1 s hs) (hxt ▸ hxs)
            · exact (hperb t ht0 htε).1 s (hmemE2 s hs) (hxt ▸ hxs)
        -- A∩B-status transfers from p to p' (segment off M); p ∉ A∩B since p ∈ ∂A.
        have hp'nAB : p' ∉ poly1.interior ∩ poly2.interior :=
          fun h => hpni1 ((hAcapB_const hpp').mpr h).1
        -- symmDiff(polys') constant from p to p'.
        have hsdiff : p ∈ symmDiffAll (polys'.map Polygon.interior) ↔
            p' ∈ symmDiffAll (polys'.map Polygon.interior) := by
          rw [mem_symmDiffAll, mem_symmDiffAll, List.countP_map, List.countP_map]
          have hcongr : List.countP ((fun s => decide (p ∈ s)) ∘ Polygon.interior) polys'
              = List.countP ((fun s => decide (p' ∈ s)) ∘ Polygon.interior) polys' := by
            apply List.countP_congr
            intro Q hQ
            simp only [Function.comp_apply, decide_eq_true_eq]
            have hbfQ : ∀ x ∈ (LineSegment.mk p p').toSet, x ∉ Q.toBoundarySet := by
              rintro x hx ⟨s, hs, hxs⟩
              exact hleg_off s (hmemEQ Q hQ s hs) (hp_offQ Q hQ s hs) x hx hxs
            exact even_odd_constancy (hnd' Q hQ) (hne' Q hQ) hbfQ
          rw [hcongr]
        -- anchor at p'.
        have hanc := anchor p' hp'A hp'B hp'v1 hp'v2 hp'offQ
        -- Assemble.
        constructor
        · intro hp
          exfalso
          have : p' ∈ poly1.interior ∩ poly2.interior := hanc.mp (hsdiff.mp hp)
          exact hp'nAB this
        · rintro ⟨hi1, _⟩; exact absurd hi1 hpni1
      · by_cases hpB : p ∈ poly2.toBoundarySet
        · -- symmetric: p ∈ ∂B, so p ∉ poly2.interior, p ∉ poly1.interior.
          have hpni2 : p ∉ poly2.interior := boundary_not_interior hpB
          have hpni1 : p ∉ poly1.interior := by
            intro h1
            obtain ⟨e, he, hpe⟩ := hMin2 p hpB h1
            exact hpM e he hpe
          obtain ⟨c, ε, hε, hperb⟩ := exists_perturb p E (poly1.vertices ++ poly2.vertices) hE_nd
          set p' : Vector2D := ⟨p.x + ε * 1, p.y + ε * c⟩ with hp'def
          have hseg_pt : ∀ x ∈ (LineSegment.mk p p').toSet, x = p ∨
              ∃ t : ℚ, 0 < t ∧ t ≤ ε ∧ x = ⟨p.x + t * 1, p.y + t * c⟩ := by
            intro x hx
            obtain ⟨u, hu0, hu1, hxx, hxy⟩ := hx
            by_cases hu : u = 0
            · left; apply Vector2D.ext
              · rw [hxx, hu]; ring
              · rw [hxy, hu]; ring
            · right
              have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
              refine ⟨u * ε, by positivity, by nlinarith [hu1, hε.le, hupos], ?_⟩
              apply Vector2D.ext
              · rw [hxx, hp'def]; ring
              · rw [hxy, hp'def]; ring
          have hp'_offE : ∀ e ∈ E, p' ∉ e.toSet := by
            intro e he
            have := (hperb ε hε (le_refl ε)).1 e he
            rw [hp'def]; exact this
          have hp'_neV : ∀ w ∈ poly1.vertices ++ poly2.vertices, p' ≠ w := by
            intro w hw
            have := (hperb ε hε (le_refl ε)).2 w hw
            rw [hp'def]; exact this
          have hleg_off : ∀ e ∈ E, p ∉ e.toSet → ∀ x ∈ (LineSegment.mk p p').toSet, x ∉ e.toSet := by
            intro e he hpe x hx
            rcases hseg_pt x hx with hxp | ⟨t, ht0, htε, hxt⟩
            · rw [hxp]; exact hpe
            · rw [hxt]; exact (hperb t ht0 htε).1 e he
          have hmemE1 : ∀ s ∈ poly1.segments, s ∈ E := fun s hs => by
            rw [hE]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hs)))
          have hmemE2 : ∀ s ∈ poly2.segments, s ∈ E := fun s hs => by
            rw [hE]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hs)))
          have hmemEQ : ∀ Q ∈ polys', ∀ s ∈ Q.segments, s ∈ E := fun Q hQ s hs => by
            rw [hE]; refine List.mem_append.mpr (Or.inr ?_)
            rw [List.mem_flatMap]; exact ⟨Q, hQ, hs⟩
          have hp_off1 : ∀ s ∈ poly1.segments, p ∉ s.toSet := fun s hs hps => hpA ⟨s, hs, hps⟩
          have hp_offQ : ∀ Q ∈ polys', ∀ s ∈ Q.segments, p ∉ s.toSet := hpoff'
          have hp'A : p' ∉ poly1.toBoundarySet := by
            rintro ⟨s, hs, hps⟩; exact hp'_offE s (hmemE1 s hs) hps
          have hp'B : p' ∉ poly2.toBoundarySet := by
            rintro ⟨s, hs, hps⟩; exact hp'_offE s (hmemE2 s hs) hps
          have hp'offQ : ∀ Q ∈ polys', ∀ s ∈ Q.segments, p' ∉ s.toSet :=
            fun Q hQ s hs => hp'_offE s (hmemEQ Q hQ s hs)
          have hp'v1 : p' ∉ poly1.vertices := fun hv =>
            hp'_neV p' (List.mem_append.mpr (Or.inl hv)) rfl
          have hp'v2 : p' ∉ poly2.vertices := fun hv =>
            hp'_neV p' (List.mem_append.mpr (Or.inr hv)) rfl
          have hp'ni1 : p' ∉ poly1.interior := by
            by_cases h1e : poly1.segments = []
            · exact notVertex_notMem_interior_of_no_segments h1e hp'v1
            · have hbf1 : ∀ x ∈ (LineSegment.mk p p').toSet, x ∉ poly1.toBoundarySet := by
                rintro x hx ⟨s, hs, hxs⟩
                exact hleg_off s (hmemE1 s hs) (hp_off1 s hs) x hx hxs
              have hcon1 : p ∈ poly1.interior ↔ p' ∈ poly1.interior :=
                even_odd_constancy h1n h1e hbf1
              exact fun h => hpni1 (hcon1.mpr h)
          have hp'nAB : p' ∉ poly1.interior ∩ poly2.interior := fun h => hp'ni1 h.1
          have hsdiff : p ∈ symmDiffAll (polys'.map Polygon.interior) ↔
              p' ∈ symmDiffAll (polys'.map Polygon.interior) := by
            rw [mem_symmDiffAll, mem_symmDiffAll, List.countP_map, List.countP_map]
            have hcongr : List.countP ((fun s => decide (p ∈ s)) ∘ Polygon.interior) polys'
                = List.countP ((fun s => decide (p' ∈ s)) ∘ Polygon.interior) polys' := by
              apply List.countP_congr
              intro Q hQ
              simp only [Function.comp_apply, decide_eq_true_eq]
              have hbfQ : ∀ x ∈ (LineSegment.mk p p').toSet, x ∉ Q.toBoundarySet := by
                rintro x hx ⟨s, hs, hxs⟩
                exact hleg_off s (hmemEQ Q hQ s hs) (hp_offQ Q hQ s hs) x hx hxs
              exact even_odd_constancy (hnd' Q hQ) (hne' Q hQ) hbfQ
            rw [hcongr]
          have hanc := anchor p' hp'A hp'B hp'v1 hp'v2 hp'offQ
          constructor
          · intro hp
            exfalso
            have : p' ∈ poly1.interior ∩ poly2.interior := hanc.mp (hsdiff.mp hp)
            exact hp'nAB this
          · rintro ⟨_, hi2⟩; exact absurd hi2 hpni2
        · -- neither: anchor directly, p ∉ vertices since off boundary (polys nonempty).
          have hpv1 : p ∉ poly1.vertices := fun hv =>
            hpA (vertex_on_boundary ((segments_ne_nil_iff poly1).1 poly1_seg_ne) hv)
          have hpv2 : p ∉ poly2.vertices := fun hv =>
            hpB (vertex_on_boundary ((segments_ne_nil_iff poly2).1 poly2_seg_ne) hv)
          exact anchor p hpA hpB hpv1 hpv2 hpoff'
    -- Assemble the existential.
    refine ⟨r, hro, havp, ?_⟩
    exact hbridge_p.symm.trans htrans
