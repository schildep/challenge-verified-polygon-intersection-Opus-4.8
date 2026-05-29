import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.Cross
import Polygons2.CrossSigns
import Polygons2.SectorCore
import Polygons2.RayIndep
import Polygons2.Interior
import Polygons2.GoodRay
import Polygons2.Clip
import Polygons2.ClipM
import Polygons2.ClipProps
import Polygons2.InsideCount

/-!
# Even degree of the clipped intersection-boundary multiset `Mlist`.

We prove `Mlist_even_degree`: for every vertex `v`, the total number of `Mlist`-edge
endpoints equal to `v` is even.

The proof is purely count-level, via the converse of ray-independence:

* For a point `p` off both polygon boundaries, any two suitable rays `r1, r2` from `p` have
  `Mlist.countP (crossB r1) ≡ Mlist.countP (crossB r2) (mod 2)` (ray-independence of the
  inside-crossing parity).
* The per-edge XOR (`per_edge`) turns `countP(crossB r1) + countP(crossB r2)` into a sum of
  `statusB`-differences over `Mlist` edges, which therefore vanishes mod 2.
* A generic `p` and a narrow sector `(d1, d2)` around the direction `p → v0` make
  `statusB d1 d2 p w = 1` only for `w = v0`, so the `statusB`-difference sum equals
  `deg_Mlist(v0)` mod 2.  Hence `deg_Mlist(v0)` is even.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-! ## A positive `δ` making `|δ E z| < |C z|` for finitely many `z`. -/

lemma exists_pos_lt_all (L : List Vector2D) (C E : Vector2D → ℚ)
    (hC : ∀ z ∈ L, C z ≠ 0) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ z ∈ L, |δ * E z| < |C z| := by
  induction L with
  | nil => exact ⟨1, by norm_num, by intro z hz; simp at hz⟩
  | cons a t ih =>
    obtain ⟨δ', hδ'0, hδ'⟩ := ih (fun z hz => hC z (List.mem_cons_of_mem _ hz))
    have hCa : C a ≠ 0 := hC a (List.mem_cons_self ..)
    -- choose δ for the head
    set εa : ℚ := |C a| / (|E a| + 1) with hεa
    have hCaabs : 0 < |C a| := abs_pos.mpr hCa
    have hden : 0 < |E a| + 1 := by positivity
    have hεa0 : 0 < εa := by rw [hεa]; positivity
    set δ : ℚ := min δ' εa with hδ
    have hδ0 : 0 < δ := lt_min hδ'0 hεa0
    refine ⟨δ, hδ0, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · -- z = a
      rw [hz]
      -- |δ * E a| ≤ δ * (|E a| + 1) ≤ εa * (|E a| + 1) = |C a|
      have h1 : |δ * E a| = δ * |E a| := by
        rw [abs_mul, abs_of_pos hδ0]
      rw [h1]
      have hle : δ ≤ εa := min_le_right _ _
      have hEa : 0 ≤ |E a| := abs_nonneg _
      calc δ * |E a| ≤ εa * |E a| := by
              exact mul_le_mul_of_nonneg_right hle hEa
        _ < εa * (|E a| + 1) := by
              have : εa * |E a| < εa * (|E a| + 1) :=
                mul_lt_mul_of_pos_left (by linarith) hεa0
              exact this
        _ = |C a| := by rw [hεa]; field_simp
    · have hle : δ ≤ δ' := min_le_left _ _
      have := hδ' z hz
      have h1 : |δ * E z| ≤ |δ' * E z| := by
        rw [abs_mul, abs_mul, abs_of_pos hδ0, abs_of_pos hδ'0]
        exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      linarith [this, h1]

/-! ## The sector directions around `e0 = v0 - p`. -/

/-- First sector direction `d1 = e0 + δ·n`, with `n ⟂ e0`. -/
def dir1 (e0 : Vector2D) (δ : ℚ) : Vector2D := ⟨e0.x - δ * e0.y, e0.y + δ * e0.x⟩

/-- Second sector direction `d2 = e0 - δ·n`. -/
def dir2 (e0 : Vector2D) (δ : ℚ) : Vector2D := ⟨e0.x + δ * e0.y, e0.y - δ * e0.x⟩

/-- `|e0|² > 0` when `e0 ≠ 0`. -/
lemma normsq_pos {e0 : Vector2D} (h : e0 ≠ ⟨0, 0⟩) : 0 < e0.x ^ 2 + e0.y ^ 2 := by
  rcases eq_or_ne e0.x 0 with hx | hx
  · rcases eq_or_ne e0.y 0 with hy | hy
    · exact absurd (by ext <;> simp [hx, hy]) h
    · have : 0 < e0.y ^ 2 := by positivity
      nlinarith [this, sq_nonneg e0.x]
  · have : 0 < e0.x ^ 2 := by positivity
    nlinarith [this, sq_nonneg e0.y]

/-- `cross (dir1 e0 δ) (dir2 e0 δ) = -2 δ |e0|²`. -/
lemma cross_dir1_dir2 (e0 : Vector2D) (δ : ℚ) :
    cross (dir1 e0 δ) (dir2 e0 δ) = -2 * δ * (e0.x ^ 2 + e0.y ^ 2) := by
  simp only [dir1, dir2, cross_def]; ring

/-- For `δ > 0` and `e0 ≠ 0`, `cross (dir1) (dir2) < 0` (in particular `≠ 0`). -/
lemma cross_dir1_dir2_neg {e0 : Vector2D} (he0 : e0 ≠ ⟨0, 0⟩) {δ : ℚ} (hδ : 0 < δ) :
    cross (dir1 e0 δ) (dir2 e0 δ) < 0 := by
  rw [cross_dir1_dir2]
  have := normsq_pos he0
  nlinarith [this, hδ]

/-- `dir1 e0 δ ≠ 0` for `δ > 0`, `e0 ≠ 0`. -/
lemma dir1_ne {e0 : Vector2D} (he0 : e0 ≠ ⟨0, 0⟩) {δ : ℚ} (hδ : 0 < δ) :
    dir1 e0 δ ≠ ⟨0, 0⟩ := by
  intro h
  have : cross (dir1 e0 δ) (dir2 e0 δ) = 0 := by rw [h]; simp [cross_def]
  exact (ne_of_lt (cross_dir1_dir2_neg he0 hδ)) this

/-- `dir2 e0 δ ≠ 0` for `δ > 0`, `e0 ≠ 0`. -/
lemma dir2_ne {e0 : Vector2D} (he0 : e0 ≠ ⟨0, 0⟩) {δ : ℚ} (hδ : 0 < δ) :
    dir2 e0 δ ≠ ⟨0, 0⟩ := by
  intro h
  have : cross (dir1 e0 δ) (dir2 e0 δ) = 0 := by rw [h]; simp [cross_def]
  exact (ne_of_lt (cross_dir1_dir2_neg he0 hδ)) this

/-- `cross (dir1 e0 δ) w = (cross e0 w) + δ · (cross n w)` where the `n`-part is computed. -/
lemma cross_dir1 (e0 w : Vector2D) (δ : ℚ) :
    cross (dir1 e0 δ) w = cross e0 w + δ * (-e0.y * w.y - e0.x * w.x) := by
  simp only [dir1, cross_def]; ring

/-- `cross (dir2 e0 δ) w = (cross e0 w) - δ · (cross n w)`. -/
lemma cross_dir2 (e0 w : Vector2D) (δ : ℚ) :
    cross (dir2 e0 δ) w = cross e0 w - δ * (-e0.y * w.y - e0.x * w.x) := by
  simp only [dir2, cross_def]; ring

/-! ## The sector status function isolates `v0`. -/

/-- With `e0 = v0 - p`, the target `v0` is in the open sector. -/
lemma statusB_target {p v0 : Vector2D} (he0 : vsub v0 p ≠ ⟨0, 0⟩) {δ : ℚ} (hδ : 0 < δ) :
    statusB (dir1 (vsub v0 p) δ) (dir2 (vsub v0 p) δ) p v0 = true := by
  set e0 := vsub v0 p with he0def
  unfold statusB
  rw [decide_eq_true_eq]
  -- the cross products
  have hve : vsub v0 p = e0 := rfl
  rw [hve]
  have hc1 : cross (dir1 e0 δ) e0 = - (δ * (e0.x ^ 2 + e0.y ^ 2)) := by
    rw [cross_dir1]; simp only [cross_self]; ring
  have hc2 : cross (dir2 e0 δ) e0 = δ * (e0.x ^ 2 + e0.y ^ 2) := by
    rw [cross_dir2]; simp only [cross_self]; ring
  have hpos := normsq_pos he0
  unfold Sect
  right
  refine ⟨cross_dir1_dir2_neg he0 hδ, ?_, ?_⟩
  · rw [hc1]; nlinarith [hpos, hδ]
  · rw [hc2]; nlinarith [hpos, hδ]

/-- With `e0 = v0 - p`, any `w` off the line `p–v0` (`cross e0 (w-p) ≠ 0`) and with the
small-`δ` bound `|δ · Ew| < |Cw|` is *not* in the open sector. -/
lemma statusB_other {p v0 w : Vector2D} {δ : ℚ} (hδ : 0 < δ)
    (he0 : vsub v0 p ≠ ⟨0, 0⟩)
    (hCne : cross (vsub v0 p) (vsub w p) ≠ 0)
    (hbound : |δ * (-(vsub v0 p).y * (vsub w p).y - (vsub v0 p).x * (vsub w p).x)|
        < |cross (vsub v0 p) (vsub w p)|) :
    statusB (dir1 (vsub v0 p) δ) (dir2 (vsub v0 p) δ) p w = false := by
  set e0 := vsub v0 p with he0def
  set wp := vsub w p with hwpdef
  set C := cross e0 wp with hCdef
  set E := (-e0.y * wp.y - e0.x * wp.x) with hEdef
  unfold statusB
  rw [decide_eq_false_iff_not]
  have hc1 : cross (dir1 e0 δ) wp = C + δ * E := by rw [cross_dir1]
  have hc2 : cross (dir2 e0 δ) wp = C - δ * E := by rw [cross_dir2]
  have ho : cross (dir1 e0 δ) (dir2 e0 δ) < 0 := cross_dir1_dir2_neg he0 hδ
  -- bound: |δ * E| < |C|
  have hb : |δ * E| < |C| := hbound
  have hbnd := abs_lt.mp hb
  unfold Sect
  rw [hc1, hc2]
  rintro (⟨hopos, _, _⟩ | ⟨_, hc1neg, hc2pos⟩)
  · linarith
  · -- C ≠ 0; split on sign of C
    rcases lt_or_gt_of_ne hCne with hCneg | hCpos
    · -- C < 0 ⇒ c2 = C - δE < 0, contradicting hc2pos
      have : C - δ * E < 0 := by
        have := hbnd.1; have := hbnd.2; rw [abs_of_neg hCneg] at hb
        rw [abs_lt] at hb; linarith [hb.1, hb.2]
      linarith
    · -- C > 0 ⇒ c1 = C + δE > 0, contradicting hc1neg
      have : 0 < C + δ * E := by
        rw [abs_of_pos hCpos] at hb; rw [abs_lt] at hb; linarith [hb.1, hb.2]
      linarith

/-! ## Step 1: ray-independence of the `Mlist` crossing parity. -/

/-- The `Mlist` crossing parity of a suitable ray `r` from `p` equals the product of the two
interior indicators of `p`, hence is independent of the ray. -/
lemma Mlist_crossParity_eq (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p : Vector2D} (hp1 : ∀ s ∈ poly1.segments, p ∉ s.toSet)
    (hp2 : ∀ s ∈ poly2.segments, p ∉ s.toSet)
    (r : Ray) (hro : r.origin = p)
    (hav1 : rayAvoidsVertices r poly1) (hav2 : rayAvoidsVertices r poly2)
    (hS : ∀ x ∈ r.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False) :
    (Mlist poly1 poly2).countP (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩)) % 2
      = (if p ∈ poly1.interior ∧ p ∈ poly2.interior then 1 else 0) := by
  rw [Mlist_countP_eq_insideCrossings poly1 poly2 r h1n h2n h1e h2e hav1 hav2 hS hfin]
  rw [insideCrossings_parity poly1 poly2 r h1n h2n hav1 hav2 hS]
  have hi1 : intersectionRayPolygonSegmentsNumber r poly1 % 2 = 1 ↔ p ∈ poly1.interior := by
    rw [mem_interior_iff poly1 p r hro hav1 h1n]
    constructor
    · intro h; exact ⟨hp1, h⟩
    · intro h; exact h.2
  have hi2 : intersectionRayPolygonSegmentsNumber r poly2 % 2 = 1 ↔ p ∈ poly2.interior := by
    rw [mem_interior_iff poly2 p r hro hav2 h2n]
    constructor
    · intro h; exact ⟨hp2, h⟩
    · intro h; exact h.2
  -- case on the two parities
  have hb1 : intersectionRayPolygonSegmentsNumber r poly1 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb2 : intersectionRayPolygonSegmentsNumber r poly2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases hP1 : p ∈ poly1.interior
  · by_cases hP2 : p ∈ poly2.interior
    · have e1 : intersectionRayPolygonSegmentsNumber r poly1 % 2 = 1 := hi1.mpr hP1
      have e2 : intersectionRayPolygonSegmentsNumber r poly2 % 2 = 1 := hi2.mpr hP2
      rw [e1, e2, if_pos ⟨hP1, hP2⟩]
    · have e2 : intersectionRayPolygonSegmentsNumber r poly2 % 2 ≠ 1 := fun h => hP2 (hi2.mp h)
      have e2' : intersectionRayPolygonSegmentsNumber r poly2 % 2 = 0 := by omega
      rw [e2', Nat.mul_zero, if_neg (by tauto)]
  · have e1 : intersectionRayPolygonSegmentsNumber r poly1 % 2 ≠ 1 := fun h => hP1 (hi1.mp h)
    have e1' : intersectionRayPolygonSegmentsNumber r poly1 % 2 = 0 := by omega
    rw [e1', Nat.zero_mul, if_neg (by tauto)]

/-! ## Step 2: per-edge XOR, summed over `Mlist`. -/

/-- `countP P1 + countP P2 ≡ countP (P1 ≠ P2) (mod 2)`. -/
lemma countP_add_modEq_xor {α : Type*} (P1 P2 : α → Bool) (l : List α) :
    (l.countP P1 + l.countP P2) % 2 = l.countP (fun a => P1 a != P2 a) % 2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    rcases Bool.eq_false_or_eq_true (P1 a) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (P2 a) with h2 | h2 <;>
      rw [h1, h2] <;> simp <;> omega

/-- The `statusB`-difference count over `Mlist` is even (it equals the XOR of the two
crossing-counts which are equal mod 2). -/
lemma Mlist_statusB_diff_even (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p d1 d2 : Vector2D} (hd1 : d1 ≠ ⟨0, 0⟩) (hd2 : d2 ≠ ⟨0, 0⟩)
    (hpar : cross d1 d2 ≠ 0)
    (hp1 : ∀ s ∈ poly1.segments, p ∉ s.toSet) (hp2 : ∀ s ∈ poly2.segments, p ∉ s.toSet)
    (hav1₁ : rayAvoidsVertices (Ray.mk p d1 hd1) poly1)
    (hav2₁ : rayAvoidsVertices (Ray.mk p d1 hd1) poly2)
    (hav1₂ : rayAvoidsVertices (Ray.mk p d2 hd2) poly1)
    (hav2₂ : rayAvoidsVertices (Ray.mk p d2 hd2) poly2)
    (hS₁ : ∀ x ∈ (Ray.mk p d1 hd1).toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False)
    (hS₂ : ∀ x ∈ (Ray.mk p d2 hd2).toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False)
    -- per-edge endpoint avoidance for both rays
    (hoff : ∀ e ∈ Mlist poly1 poly2,
        e.1 ∉ (Ray.mk p d1 hd1).toSet ∧ e.2 ∉ (Ray.mk p d1 hd1).toSet ∧
        e.1 ∉ (Ray.mk p d2 hd2).toSet ∧ e.2 ∉ (Ray.mk p d2 hd2).toSet) :
    (Mlist poly1 poly2).countP (fun e => statusB d1 d2 p e.1 != statusB d1 d2 p e.2) % 2 = 0 := by
  set r1 : Ray := Ray.mk p d1 hd1 with hr1
  set r2 : Ray := Ray.mk p d2 hd2 with hr2
  -- the two crossing-counts are equal mod 2
  have hstep1 :
      (Mlist poly1 poly2).countP (fun e => decide (rayIntersectsSegment r1 ⟨e.1, e.2⟩)) % 2
        = (Mlist poly1 poly2).countP (fun e => decide (rayIntersectsSegment r2 ⟨e.1, e.2⟩)) % 2 := by
    rw [Mlist_crossParity_eq poly1 poly2 h1n h2n h1e h2e hfin hp1 hp2 r1 rfl hav1₁ hav2₁ hS₁,
        Mlist_crossParity_eq poly1 poly2 h1n h2n h1e h2e hfin hp1 hp2 r2 rfl hav1₂ hav2₂ hS₂]
  -- XOR count = sum of the two crossing counts mod 2 = 0
  have hxor := countP_add_modEq_xor
    (fun e => decide (rayIntersectsSegment r1 ⟨e.1, e.2⟩))
    (fun e => decide (rayIntersectsSegment r2 ⟨e.1, e.2⟩)) (Mlist poly1 poly2)
  -- per edge, the xor equals statusB difference
  have hcongr : (Mlist poly1 poly2).countP
      (fun e => decide (rayIntersectsSegment r1 ⟨e.1, e.2⟩)
        != decide (rayIntersectsSegment r2 ⟨e.1, e.2⟩))
      = (Mlist poly1 poly2).countP (fun e => statusB d1 d2 p e.1 != statusB d1 d2 p e.2) := by
    apply List.countP_congr
    intro e he
    have hnd : e.1 ≠ e.2 := Mlist_nondeg poly1 poly2 e he
    have hps : p ∉ (LineSegment.mk e.1 e.2).toSet := by
      -- p off both boundaries, but the edge lies in a boundary; so p not on the edge
      have hsub := Mlist_subset_boundary poly1 poly2 e he
      intro hp
      rcases hsub p hp with h1 | h2
      · obtain ⟨s, hs, hm⟩ := h1; exact hp1 s hs hm
      · obtain ⟨s, hs, hm⟩ := h2; exact hp2 s hs hm
    obtain ⟨ha1, hb1, ha2, hb2⟩ := hoff e he
    have hpe := per_edge p d1 d2 e.1 e.2 hd1 hd2 hpar hnd hps ha1 hb1 ha2 hb2
    -- hpe is a Bool equality; r1, r2 are defeq to the explicit rays
    show (decide (rayIntersectsSegment r1 ⟨e.1, e.2⟩)
        != decide (rayIntersectsSegment r2 ⟨e.1, e.2⟩)) = true
      ↔ (statusB d1 d2 p e.1 != statusB d1 d2 p e.2) = true
    rw [hr1, hr2, hpe]
  rw [hcongr] at hxor
  omega

/-! ## Genericity: a point off finitely many lines and points. -/

/-- A `Vector2D` is off the line through `P ≠ Q` iff `cross (Q-P) (p-P) ≠ 0`. -/
lemma exists_generic_point (lineList : List (Vector2D × Vector2D)) (ptList : List Vector2D)
    (hlines : ∀ l ∈ lineList, l.1 ≠ l.2) :
    ∃ p : Vector2D,
      (∀ l ∈ lineList, cross (vsub l.2 l.1) (vsub p l.1) ≠ 0) ∧
      (∀ z ∈ ptList, p ≠ z) := by
  -- Step 1: choose a slope `k` so that `⟨1,k⟩` is not parallel to any line direction.
  set Bk : Finset ℚ :=
    (lineList.map (fun l => (l.2.y - l.1.y) / (l.2.x - l.1.x))).toFinset with hBk
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset Bk
  have hkpar : ∀ l ∈ lineList, cross (⟨1, k⟩ : Vector2D) (vsub l.2 l.1) ≠ 0 := by
    intro l hl
    simp only [cross_def, vsub_x, vsub_y, one_mul]
    rcases eq_or_ne (l.2.x - l.1.x) 0 with hx | hx
    · -- vertical line direction; cross = (l.2.y - l.1.y) - k*0 = l.2.y - l.1.y ≠ 0
      have hy : l.2.y - l.1.y ≠ 0 := by
        intro hy
        apply hlines l hl
        have : l.1 = l.2 := by
          ext
          · have := hx; linarith
          · have := hy; linarith
        exact this.symm ▸ rfl
      rw [hx]; simpa using hy
    · intro hc
      apply hk
      rw [hBk, List.mem_toFinset, List.mem_map]
      refine ⟨l, hl, ?_⟩
      field_simp
      linarith [hc]
  -- Step 2: with `p = ⟨s, k*s⟩`, choose `s` avoiding finitely many bad values.
  set Bs : Finset ℚ :=
    (lineList.map (fun l =>
      ((l.2.x - l.1.x) * l.1.y - (l.2.y - l.1.y) * l.1.x)
        / ((l.2.x - l.1.x) * k - (l.2.y - l.1.y)))).toFinset
    ∪ (ptList.map (fun z => z.x)).toFinset with hBs
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset Bs
  refine ⟨⟨s, k * s⟩, ?_, ?_⟩
  · intro l hl
    -- coefficient of s
    set cf : ℚ := (l.2.x - l.1.x) * k - (l.2.y - l.1.y) with hcf
    have hcfne : cf ≠ 0 := by
      have := hkpar l hl
      simp only [cross_def, vsub_x, vsub_y, one_mul] at this
      rw [hcf]; intro h; apply this; linarith
    intro hc
    -- hc : cross (Q-P) (p-P) = 0 with p = ⟨s, k*s⟩
    simp only [cross_def, vsub_x, vsub_y] at hc
    -- s * cf = const, so s = const / cf
    have hseq : s * cf = (l.2.x - l.1.x) * l.1.y - (l.2.y - l.1.y) * l.1.x := by
      rw [hcf]; nlinarith [hc]
    apply hs
    rw [hBs, Finset.mem_union]; left
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨l, hl, ?_⟩
    rw [eq_comm, eq_div_iff hcfne]
    exact hseq
  · intro z hz hpz
    -- p = z ⇒ s = z.x
    have hsx : s = z.x := by
      have := congrArg Vector2D.x hpz; simpa using this
    apply hs
    rw [hBs, Finset.mem_union]; right
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨z, hz, hsx.symm⟩

/-- A point on the segment `[a,b]` is collinear: `cross (b-a) (p-a) = 0`. -/
lemma cross_zero_of_mem_seg {a b p : Vector2D} (hp : p ∈ (LineSegment.mk a b).toSet) :
    cross (vsub b a) (vsub p a) = 0 := by
  obtain ⟨t, _, _, hx, hy⟩ := hp
  simp only [cross_def, vsub_x, vsub_y, hx, hy]; ring

/-- Off the supporting line ⇒ off the segment. -/
lemma not_mem_seg_of_cross_ne {a b p : Vector2D}
    (h : cross (vsub b a) (vsub p a) ≠ 0) : p ∉ (LineSegment.mk a b).toSet :=
  fun hp => h (cross_zero_of_mem_seg hp)

/-- If `cross d (z-p) ≠ 0`, then `z` is not on the ray from `p` in direction `d`. -/
lemma not_mem_ray_of_cross_ne {p d z : Vector2D} (hd : d ≠ ⟨0, 0⟩)
    (h : cross d (vsub z p) ≠ 0) : z ∉ (Ray.mk p d hd).toSet := by
  intro hz
  rw [mem_ray_iff] at hz
  exact h hz.1

/-- A bad point `z` is off the line of `dir1 e0 δ` (from `p`), under the genericity / bound. -/
lemma cross_dir1_ne {p v0 z : Vector2D} {δ : ℚ} (hδ : 0 < δ)
    (he0 : vsub v0 p ≠ ⟨0, 0⟩)
    (hz : z = v0 ∨ (cross (vsub v0 p) (vsub z p) ≠ 0 ∧
        |δ * (-(vsub v0 p).y * (vsub z p).y - (vsub v0 p).x * (vsub z p).x)|
          < |cross (vsub v0 p) (vsub z p)|)) :
    cross (dir1 (vsub v0 p) δ) (vsub z p) ≠ 0 := by
  set e0 := vsub v0 p with he0def
  rcases hz with hz | ⟨hCne, hbound⟩
  · subst hz
    have : cross (dir1 e0 δ) e0 = - (δ * (e0.x ^ 2 + e0.y ^ 2)) := by
      rw [cross_dir1]; simp only [cross_self]; ring
    rw [this]
    have hpos := normsq_pos he0
    intro h; nlinarith [hpos, hδ]
  · set wp := vsub z p with hwp
    have hc1 : cross (dir1 e0 δ) wp
        = cross e0 wp + δ * (-e0.y * wp.y - e0.x * wp.x) := by rw [cross_dir1]
    rw [hc1]
    have hbnd := abs_lt.mp hbound
    rcases lt_or_gt_of_ne hCne with hCneg | hCpos
    · rw [abs_of_neg hCneg] at hbound; rw [abs_lt] at hbound
      intro h; linarith [hbound.1, hbound.2]
    · rw [abs_of_pos hCpos] at hbound; rw [abs_lt] at hbound
      intro h; linarith [hbound.1, hbound.2]

/-- A bad point `z` is off the line of `dir2 e0 δ` (from `p`), under the genericity / bound. -/
lemma cross_dir2_ne {p v0 z : Vector2D} {δ : ℚ} (hδ : 0 < δ)
    (he0 : vsub v0 p ≠ ⟨0, 0⟩)
    (hz : z = v0 ∨ (cross (vsub v0 p) (vsub z p) ≠ 0 ∧
        |δ * (-(vsub v0 p).y * (vsub z p).y - (vsub v0 p).x * (vsub z p).x)|
          < |cross (vsub v0 p) (vsub z p)|)) :
    cross (dir2 (vsub v0 p) δ) (vsub z p) ≠ 0 := by
  set e0 := vsub v0 p with he0def
  rcases hz with hz | ⟨hCne, hbound⟩
  · subst hz
    have : cross (dir2 e0 δ) e0 = δ * (e0.x ^ 2 + e0.y ^ 2) := by
      rw [cross_dir2]; simp only [cross_self]; ring
    rw [this]
    have hpos := normsq_pos he0
    intro h; nlinarith [hpos, hδ]
  · set wp := vsub z p with hwp
    have hc2 : cross (dir2 e0 δ) wp
        = cross e0 wp - δ * (-e0.y * wp.y - e0.x * wp.x) := by rw [cross_dir2]
    rw [hc2]
    have hbnd := abs_lt.mp hbound
    rcases lt_or_gt_of_ne hCne with hCneg | hCpos
    · rw [abs_of_neg hCneg] at hbound; rw [abs_lt] at hbound
      intro h; linarith [hbound.1, hbound.2]
    · rw [abs_of_pos hCpos] at hbound; rw [abs_lt] at hbound
      intro h; linarith [hbound.1, hbound.2]

/-! ## Step 3: from the `statusB`-difference count to the degree. -/

/-- The list of all `Mlist`-edge endpoints. -/
def Mverts (poly1 poly2 : Polygon) : List Vector2D :=
  (Mlist poly1 poly2).map Prod.fst ++ (Mlist poly1 poly2).map Prod.snd

lemma fst_mem_Mverts {poly1 poly2 : Polygon} {e : Vector2D × Vector2D}
    (he : e ∈ Mlist poly1 poly2) : e.1 ∈ Mverts poly1 poly2 := by
  unfold Mverts; rw [List.mem_append]; left
  rw [List.mem_map]; exact ⟨e, he, rfl⟩

lemma snd_mem_Mverts {poly1 poly2 : Polygon} {e : Vector2D × Vector2D}
    (he : e ∈ Mlist poly1 poly2) : e.2 ∈ Mverts poly1 poly2 := by
  unfold Mverts; rw [List.mem_append]; right
  rw [List.mem_map]; exact ⟨e, he, rfl⟩

/-- If `statusB d1 d2 p w = decide (w = v0)` for every `Mlist`-endpoint `w`, and the
`statusB`-difference count over `Mlist` is even, then `deg_Mlist v0` is even. -/
lemma deg_even_of_statusB (poly1 poly2 : Polygon) {p d1 d2 v0 : Vector2D}
    (hstat : ∀ w ∈ Mverts poly1 poly2, statusB d1 d2 p w = decide (w = v0))
    (heven : (Mlist poly1 poly2).countP
        (fun e => statusB d1 d2 p e.1 != statusB d1 d2 p e.2) % 2 = 0) :
    ((Mlist poly1 poly2).countP (fun e => decide (e.1 = v0))
        + (Mlist poly1 poly2).countP (fun e => decide (e.2 = v0))) % 2 = 0 := by
  -- rewrite the statusB-diff count as the (decide = v0) xor count
  have hcongr : (Mlist poly1 poly2).countP
      (fun e => statusB d1 d2 p e.1 != statusB d1 d2 p e.2)
      = (Mlist poly1 poly2).countP
          (fun e => decide (e.1 = v0) != decide (e.2 = v0)) := by
    apply List.countP_congr
    intro e he
    have h1 := hstat e.1 (fst_mem_Mverts he)
    have h2 := hstat e.2 (snd_mem_Mverts he)
    rw [h1, h2]
  rw [hcongr] at heven
  rw [countP_add_modEq_xor (fun e => decide (e.1 = v0)) (fun e => decide (e.2 = v0))
    (Mlist poly1 poly2)]
  exact heven

/-! ## Main theorem. -/

theorem Mlist_even_degree (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet)) :
    ∀ v : Vector2D, ((Mlist poly1 poly2).countP (fun e => decide (e.1 = v))
        + (Mlist poly1 poly2).countP (fun e => decide (e.2 = v))) % 2 = 0 := by
  intro v0
  -- list of all "bad" points the constructed rays must avoid
  set Slist : List Vector2D := hfin.toFinset.toList with hSlist
  set BadPts : List Vector2D :=
    poly1.vertices ++ poly2.vertices ++ Slist ++ Mverts poly1 poly2 with hBad
  -- points of BadPts distinct from v0
  set BadNe : List Vector2D := BadPts.filter (fun z => decide (z ≠ v0)) with hBadNe
  -- the lines p must avoid: polygon edges and lines through v0 and each bad point ≠ v0
  set edgePairs : List (Vector2D × Vector2D) :=
    (poly1.segments ++ poly2.segments).map (fun e => (e.p1, e.p2)) with hEdge
  set linePairs : List (Vector2D × Vector2D) :=
    edgePairs ++ BadNe.map (fun z => (v0, z)) with hLine
  -- nondegeneracy of all lines
  have hlines : ∀ l ∈ linePairs, l.1 ≠ l.2 := by
    intro l hl
    rw [hLine, List.mem_append] at hl
    rcases hl with hl | hl
    · rw [hEdge, List.mem_map] at hl
      obtain ⟨e, he, rfl⟩ := hl
      simp only
      rw [List.mem_append] at he
      rcases he with he | he
      · exact h1n e he
      · exact h2n e he
    · rw [List.mem_map] at hl
      obtain ⟨z, hz, rfl⟩ := hl
      simp only
      rw [hBadNe, List.mem_filter, decide_eq_true_eq] at hz
      exact (Ne.symm hz.2)
  -- choose generic p
  obtain ⟨p, hpoff, hpne⟩ := exists_generic_point linePairs [v0] hlines
  have hpv0 : p ≠ v0 := hpne v0 (List.mem_cons_self ..)
  -- e0 = v0 - p ≠ 0
  set e0 := vsub v0 p with he0def
  have he0 : e0 ≠ ⟨0, 0⟩ := by
    intro h
    apply hpv0
    have hx : v0.x - p.x = 0 := by have := congrArg Vector2D.x h; simpa [vsub] using this
    have hy : v0.y - p.y = 0 := by have := congrArg Vector2D.y h; simpa [vsub] using this
    ext <;> [linarith; linarith]
  -- the genericity collinearity facts for bad points ≠ v0
  have hCne : ∀ z ∈ BadNe, cross e0 (vsub z p) ≠ 0 := by
    intro z hz
    -- (v0, z) ∈ linePairs
    have hmem : ((v0, z) : Vector2D × Vector2D) ∈ linePairs := by
      rw [hLine, List.mem_append]; right
      rw [List.mem_map]; exact ⟨z, hz, rfl⟩
    have := hpoff (v0, z) hmem
    simp only at this
    -- this : cross (vsub z v0) (vsub p v0) ≠ 0 ; equals cross (vsub v0 p) (vsub z p)
    rw [he0def]
    intro hc; apply this
    simp only [cross_def, vsub_x, vsub_y] at hc ⊢
    nlinarith [hc]
  -- choose δ
  obtain ⟨δ, hδ0, hδbound⟩ := exists_pos_lt_all BadNe
    (fun z => cross e0 (vsub z p))
    (fun z => (-(e0).y * (vsub z p).y - (e0).x * (vsub z p).x))
    hCne
  -- abbreviate the two directions and rays
  set d1 := dir1 e0 δ with hd1def
  set d2 := dir2 e0 δ with hd2def
  have hd1ne : d1 ≠ ⟨0, 0⟩ := dir1_ne he0 hδ0
  have hd2ne : d2 ≠ ⟨0, 0⟩ := dir2_ne he0 hδ0
  set r1 : Ray := Ray.mk p d1 hd1ne with hr1
  set r2 : Ray := Ray.mk p d2 hd2ne with hr2
  -- KEY: every bad point is off both rays, and its statusB = decide(z = v0)
  -- prepare the per-point disjunct
  have hdisj : ∀ z ∈ BadPts, z = v0 ∨ (cross e0 (vsub z p) ≠ 0 ∧
      |δ * (-(e0).y * (vsub z p).y - (e0).x * (vsub z p).x)| < |cross e0 (vsub z p)|) := by
    intro z hz
    by_cases hzv : z = v0
    · left; exact hzv
    · right
      have hmemNe : z ∈ BadNe := by
        rw [hBadNe, List.mem_filter, decide_eq_true_eq]; exact ⟨hz, hzv⟩
      exact ⟨hCne z hmemNe, hδbound z hmemNe⟩
  have hoffray : ∀ z ∈ BadPts, z ∉ r1.toSet ∧ z ∉ r2.toSet := by
    intro z hz
    have hd := hdisj z hz
    constructor
    · rw [hr1]; exact not_mem_ray_of_cross_ne hd1ne
        (by rw [hd1def, he0def] at *; exact cross_dir1_ne hδ0 he0 (by rw [he0def] at hd; exact hd))
    · rw [hr2]; exact not_mem_ray_of_cross_ne hd2ne
        (by rw [hd2def, he0def] at *; exact cross_dir2_ne hδ0 he0 (by rw [he0def] at hd; exact hd))
  have hstatBad : ∀ z ∈ BadPts, statusB d1 d2 p z = decide (z = v0) := by
    intro z hz
    by_cases hzv : z = v0
    · subst hzv
      rw [hd1def, hd2def, he0def]
      rw [statusB_target he0 hδ0]
      simp
    · rw [hd1def, hd2def, he0def]
      have hmemNe : z ∈ BadNe := by
        rw [hBadNe, List.mem_filter, decide_eq_true_eq]; exact ⟨hz, hzv⟩
      rw [statusB_other hδ0 he0 (hCne z hmemNe) (hδbound z hmemNe)]
      simp [hzv]
  -- subset facts
  have hsub_v1 : ∀ z ∈ poly1.vertices, z ∈ BadPts := by
    intro z hz; rw [hBad]; rw [List.mem_append, List.mem_append, List.mem_append]
    left; left; left; exact hz
  have hsub_v2 : ∀ z ∈ poly2.vertices, z ∈ BadPts := by
    intro z hz; rw [hBad]; rw [List.mem_append, List.mem_append, List.mem_append]
    left; left; right; exact hz
  have hsub_S : ∀ z ∈ Slist, z ∈ BadPts := by
    intro z hz; rw [hBad]; rw [List.mem_append, List.mem_append]
    left; right; exact hz
  have hsub_M : ∀ z ∈ Mverts poly1 poly2, z ∈ BadPts := by
    intro z hz; rw [hBad]; rw [List.mem_append]
    right; exact hz
  -- p off both boundaries
  have hp1 : ∀ s ∈ poly1.segments, p ∉ s.toSet := by
    intro s hs
    have hmem : ((s.p1, s.p2) : Vector2D × Vector2D) ∈ linePairs := by
      rw [hLine, List.mem_append]; left
      rw [hEdge, List.mem_map]
      exact ⟨s, List.mem_append_left _ hs, rfl⟩
    have := hpoff (s.p1, s.p2) hmem
    simp only at this
    have hns : s = LineSegment.mk s.p1 s.p2 := by cases s; rfl
    rw [hns]
    exact not_mem_seg_of_cross_ne this
  have hp2 : ∀ s ∈ poly2.segments, p ∉ s.toSet := by
    intro s hs
    have hmem : ((s.p1, s.p2) : Vector2D × Vector2D) ∈ linePairs := by
      rw [hLine, List.mem_append]; left
      rw [hEdge, List.mem_map]
      exact ⟨s, List.mem_append_right _ hs, rfl⟩
    have := hpoff (s.p1, s.p2) hmem
    simp only at this
    have hns : s = LineSegment.mk s.p1 s.p2 := by cases s; rfl
    rw [hns]
    exact not_mem_seg_of_cross_ne this
  -- rayAvoidsVertices for both polys and both rays
  have hav1₁ : rayAvoidsVertices r1 poly1 := by
    rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzr, hzv⟩
    exact (hoffray z (hsub_v1 z hzv)).1 hzr
  have hav2₁ : rayAvoidsVertices r1 poly2 := by
    rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzr, hzv⟩
    exact (hoffray z (hsub_v2 z hzv)).1 hzr
  have hav1₂ : rayAvoidsVertices r2 poly1 := by
    rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzr, hzv⟩
    exact (hoffray z (hsub_v1 z hzv)).2 hzr
  have hav2₂ : rayAvoidsVertices r2 poly2 := by
    rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzr, hzv⟩
    exact (hoffray z (hsub_v2 z hzv)).2 hzr
  -- S-avoidance
  have hmem_S : ∀ z, z ∈ poly1.toBoundarySet → z ∈ poly2.toBoundarySet → z ∈ Slist := by
    intro z hz1 hz2
    rw [hSlist, Finset.mem_toList]
    rw [Set.Finite.mem_toFinset]
    exact ⟨hz1, hz2⟩
  have hS₁ : ∀ x ∈ r1.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False := by
    intro x hxr hx1 hx2
    exact (hoffray x (hsub_S x (hmem_S x hx1 hx2))).1 hxr
  have hS₂ : ∀ x ∈ r2.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False := by
    intro x hxr hx1 hx2
    exact (hoffray x (hsub_S x (hmem_S x hx1 hx2))).2 hxr
  -- per-edge endpoint avoidance
  have hoff : ∀ e ∈ Mlist poly1 poly2,
      e.1 ∉ r1.toSet ∧ e.2 ∉ r1.toSet ∧ e.1 ∉ r2.toSet ∧ e.2 ∉ r2.toSet := by
    intro e he
    have h1 := hoffray e.1 (hsub_M e.1 (fst_mem_Mverts he))
    have h2 := hoffray e.2 (hsub_M e.2 (snd_mem_Mverts he))
    exact ⟨h1.1, h2.1, h1.2, h2.2⟩
  -- non-parallel
  have hpar : cross d1 d2 ≠ 0 := by
    rw [hd1def, hd2def]; exact ne_of_lt (cross_dir1_dir2_neg he0 hδ0)
  -- statusB-difference count is even
  have heven := Mlist_statusB_diff_even poly1 poly2 h1n h2n h1e h2e hfin hd1ne hd2ne hpar
    hp1 hp2 hav1₁ hav2₁ hav1₂ hav2₂ hS₁ hS₂ hoff
  -- statusB on Mverts equals decide(· = v0)
  have hstat : ∀ w ∈ Mverts poly1 poly2, statusB d1 d2 p w = decide (w = v0) :=
    fun w hw => hstatBad w (hsub_M w hw)
  exact deg_even_of_statusB poly1 poly2 hstat heven

end Polygons2
end
