import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.Cross
import Polygons2.CrossSigns
import Polygons2.SectorCore
import Polygons2.Telescope
import Polygons2.Independence
import Polygons2.GoodRay

/-!
# Ray-independence of crossing parity.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-- Status of a vertex `v` w.r.t. two ray directions (in the open angular sector). -/
def statusB (d1 d2 p v : Vector2D) : Bool :=
  decide (Sect (cross d1 (vsub v p)) (cross d2 (vsub v p)) (cross d1 d2))

/-- Bool helper: equal-up-to-iff transfers through `!=` of decides. -/
lemma bne_decide (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S]
    (h : (P ↔ Q) ↔ (R ↔ S)) : (decide P != decide Q) = (decide R != decide S) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> by_cases hS : S <;>
    simp_all [decide_eq_true_eq] <;> tauto

/-- Per-edge: for non-parallel rays from `p`, the XOR of "ray crosses edge `ab`" equals
the XOR of the sector-statuses of the endpoints. -/
lemma per_edge (p d1 d2 a b : Vector2D) (hd1 : d1 ≠ ⟨0, 0⟩) (hd2 : d2 ≠ ⟨0, 0⟩)
    (ho : cross d1 d2 ≠ 0) (hab : a ≠ b)
    (hp : p ∉ (LineSegment.mk a b).toSet)
    (ha1 : a ∉ (Ray.mk p d1 hd1).toSet) (hb1 : b ∉ (Ray.mk p d1 hd1).toSet)
    (ha2 : a ∉ (Ray.mk p d2 hd2).toSet) (hb2 : b ∉ (Ray.mk p d2 hd2).toSet) :
    (decide (rayIntersectsSegment (Ray.mk p d1 hd1) ⟨a, b⟩)
        != decide (rayIntersectsSegment (Ray.mk p d2 hd2) ⟨a, b⟩))
      = (statusB d1 d2 p a != statusB d1 d2 p b) := by
  have h1 := crossB_iff (Ray.mk p d1 hd1) a b hp ha1 hb1
  have h2 := crossB_iff (Ray.mk p d2 hd2) a b hp ha2 hb2
  have hR : (cross d1 d2) * (cross (vsub b a) (vsub a p))
      = (cross d1 (vsub b p)) * (cross d2 (vsub a p))
        - (cross d1 (vsub a p)) * (cross d2 (vsub b p)) := by
    simp only [cross_def, vsub_x, vsub_y]; ring
  have Ha1 : cross d1 (vsub a p) = 0 → 0 < cross d2 (vsub a p) * cross d1 d2 :=
    fun hc => sign_fact p d1 d2 a hd1 ho ha1 hc
  have Hb1 : cross d1 (vsub b p) = 0 → 0 < cross d2 (vsub b p) * cross d1 d2 :=
    fun hc => sign_fact p d1 d2 b hd1 ho hb1 hc
  have hcd : cross d2 d1 = - cross d1 d2 := by simp only [cross_def]; ring
  have ho' : cross d2 d1 ≠ 0 := by rw [hcd]; exact neg_ne_zero.mpr ho
  have Ha2 : cross d2 (vsub a p) = 0 → cross d1 (vsub a p) * cross d1 d2 < 0 := by
    intro hc
    have hh := sign_fact p d2 d1 a hd2 ho' ha2 hc
    rw [hcd] at hh; nlinarith [hh]
  have Hb2 : cross d2 (vsub b p) = 0 → cross d1 (vsub b p) * cross d1 d2 < 0 := by
    intro hc
    have hh := sign_fact p d2 d1 b hd2 ho' hb2 hc
    rw [hcd] at hh; nlinarith [hh]
  have HK : cross (vsub b a) (vsub a p) = 0 →
      (0 ≤ cross d1 (vsub a p) * cross d1 (vsub b p)
        ∧ 0 ≤ cross d2 (vsub a p) * cross d2 (vsub b p)) := by
    intro hK0
    exact ⟨sign_fact_K p a b d1 hab hp hK0, sign_fact_K p a b d2 hab hp hK0⟩
  have hsec := sector_core (cross d1 (vsub a p)) (cross d1 (vsub b p))
    (cross d2 (vsub a p)) (cross d2 (vsub b p)) (cross (vsub b a) (vsub a p)) (cross d1 d2)
    ho hR Ha1 Hb1 Ha2 Hb2 HK
  unfold statusB
  apply bne_decide
  rw [h1, h2]
  exact hsec

/-- A vertex of `poly` is not on a ray that avoids the polygon's vertices. -/
lemma vertex_not_on_ray {poly : Polygon} {r : Ray} (hav : rayAvoidsVertices r poly)
    {w : Vector2D} (hw : w ∈ poly.vertices) : w ∉ r.toSet := by
  intro hwr
  have hmem : w ∈ r.toSet ∩ poly.toVertices := ⟨hwr, hw⟩
  rw [hav] at hmem
  exact hmem

/-- Core: two non-parallel vertex-avoiding rays give equal crossing parity. -/
theorem ray_indep_ne (poly : Polygon) (p : Vector2D)
    (hpoff : ∀ s ∈ poly.segments, p ∉ s.toSet)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (r1 r2 : Ray) (h1o : r1.origin = p) (h2o : r2.origin = p)
    (hav1 : rayAvoidsVertices r1 poly) (hav2 : rayAvoidsVertices r2 poly)
    (ho : cross r1.direction r2.direction ≠ 0) :
    intersectionRayPolygonSegmentsNumber r1 poly % 2
      = intersectionRayPolygonSegmentsNumber r2 poly % 2 := by
  obtain ⟨o1, d1, hd1⟩ := r1
  obtain ⟨o2, d2, hd2⟩ := r2
  simp only at h1o h2o ho hav1 hav2
  subst o1; subst o2
  unfold intersectionRayPolygonSegmentsNumber
  apply countP_parity_of_xor_even
  have key : (poly.segments.countP fun s =>
        decide (rayIntersectsSegment ⟨p, d1, hd1⟩ s)
          != decide (rayIntersectsSegment ⟨p, d2, hd2⟩ s))
      = poly.segments.countP fun s => statusB d1 d2 p s.p1 != statusB d1 d2 p s.p2 := by
    apply List.countP_congr
    intro s hs
    obtain ⟨hmem1, hmem2⟩ := seg_mem_vertices hs
    have ha1 : s.p1 ∉ (Ray.mk p d1 hd1).toSet := vertex_not_on_ray hav1 hmem1
    have hb1 : s.p2 ∉ (Ray.mk p d1 hd1).toSet := vertex_not_on_ray hav1 hmem2
    have ha2 : s.p1 ∉ (Ray.mk p d2 hd2).toSet := vertex_not_on_ray hav2 hmem1
    have hb2 : s.p2 ∉ (Ray.mk p d2 hd2).toSet := vertex_not_on_ray hav2 hmem2
    have hps : p ∉ (LineSegment.mk s.p1 s.p2).toSet := hpoff s hs
    have hpe : (decide (rayIntersectsSegment ⟨p, d1, hd1⟩ s)
          != decide (rayIntersectsSegment ⟨p, d2, hd2⟩ s))
        = (statusB d1 d2 p s.p1 != statusB d1 d2 p s.p2) :=
      per_edge p d1 d2 s.p1 s.p2 hd1 hd2 ho (hnd s hs) hps ha1 hb1 ha2 hb2
    rw [hpe]
  rw [key]
  exact segments_countP_change_even poly (statusB d1 d2 p)

/-- Ray-independence: any two vertex-avoiding rays from `p` give equal crossing parity. -/
theorem ray_indep (poly : Polygon) (p : Vector2D)
    (hpoff : ∀ s ∈ poly.segments, p ∉ s.toSet)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (r1 r2 : Ray) (h1o : r1.origin = p) (h2o : r2.origin = p)
    (hav1 : rayAvoidsVertices r1 poly) (hav2 : rayAvoidsVertices r2 poly) :
    intersectionRayPolygonSegmentsNumber r1 poly % 2
      = intersectionRayPolygonSegmentsNumber r2 poly % 2 := by
  by_cases ho : cross r1.direction r2.direction = 0
  · -- parallel: route through a non-parallel good intermediary
    have hp_on : p ∈ r1.toSet := by
      rw [← h1o]; exact ⟨0, le_refl _, by simp, by simp⟩
    have hpV : ∀ w ∈ poly.vertices, w ≠ p := by
      intro w hw hwp
      exact vertex_not_on_ray hav1 hw (hwp.symm ▸ hp_on)
    obtain ⟨k, hk1, hk2, hkav⟩ := exists_good_dir p r1.direction r2.direction poly.vertices
      r1.direction_nonzero r2.direction_nonzero hpV
    have hd3 : (⟨1, k⟩ : Vector2D) ≠ ⟨0, 0⟩ := by
      intro h; simp [Vector2D.ext_iff] at h
    have hav3 : rayAvoidsVertices (⟨p, ⟨1, k⟩, hd3⟩ : Ray) poly := by
      rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
      rintro w ⟨hwr, hwv⟩
      obtain ⟨t, ht0, htx, hty⟩ := hwr
      exact hkav w hwv ⟨t, ht0, htx, hty⟩
    have e13 := ray_indep_ne poly p hpoff hnd r1 (⟨p, ⟨1, k⟩, hd3⟩ : Ray) h1o rfl hav1 hav3 hk1
    have e23 := ray_indep_ne poly p hpoff hnd r2 (⟨p, ⟨1, k⟩, hd3⟩ : Ray) h2o rfl hav2 hav3 hk2
    rw [e13, e23]
  · exact ray_indep_ne poly p hpoff hnd r1 r2 h1o h2o hav1 hav2 ho

end Polygons2
end
