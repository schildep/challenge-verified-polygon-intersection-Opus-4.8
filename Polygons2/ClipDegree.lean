import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.RayIndep
import Polygons2.Interior
import Polygons2.SubRay
import Polygons2.RayParam
import Polygons2.Clip
import Polygons2.InsideCount
import Polygons2.ClipM
import Polygons2.Constancy
import Polygons2.ClipProps

/-!
# One-crossing flip machinery for the clipped intersection boundary `Mlist`.

This file develops the reusable infrastructure for the one-crossing FLIP described in the
project strategy:

* `countP_ge_split` / `subRay_count_window` : the crossing count of a sub-ray changes by exactly
  the number of crossing parameters in the half-open window `[t₁,t₂)`.
* `flip_subRay_one` : the **one-crossing flip in sub-ray form** — if a vertex-avoiding ray has
  exactly one crossing parameter in the window and both sub-ray origins are off `poly`'s boundary,
  the two origins have *opposite* `poly.interior` status.  This is the count-`= 1` analogue of
  `ClipM.flip_subRay` (the count-`= 0` case).
* `Psh` / `legPsh_close` / `legPt_edge_bf` / `legPt_bf` : the parallel-shift perturbation moving
  an endpoint `v` (lying on the line `[P,Q]`, off `poly`'s boundary) to `v + k·n`
  (`n ⊥ (Q−P)`), with the connecting leg `[v, v+k·n]` boundary-free for small `k`
  (so `even_odd_constancy` transfers interior status across it).

These are exactly the pieces the strategy prescribes for `even_odd_flip` and, through it,
`S_subset_Mlist` and `Mlist_even_degree`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-! ## Counting threshold crossings: the count drops by the number of params in `[t₁,t₂)`. -/

/-- For a list of rationals and `t₁ ≤ t₂`, the number `≥ t₁` equals the number `≥ t₂` plus the
number in the half-open window `[t₁,t₂)`. -/
lemma countP_ge_split (L : List ℚ) {t₁ t₂ : ℚ} (h : t₁ ≤ t₂) :
    L.countP (fun u => decide (t₁ ≤ u))
      = L.countP (fun u => decide (t₂ ≤ u))
        + L.countP (fun u => decide (t₁ ≤ u ∧ u < t₂)) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, ih]
    have key : (if decide (t₁ ≤ a) = true then (1:ℕ) else 0)
        = (if decide (t₂ ≤ a) = true then 1 else 0)
          + (if decide (t₁ ≤ a ∧ a < t₂) = true then 1 else 0) := by
      by_cases h1 : t₁ ≤ a
      · by_cases h2 : t₂ ≤ a
        · have h3 : ¬ (t₁ ≤ a ∧ a < t₂) := by rintro ⟨_, hlt⟩; linarith
          simp [h1, h2, h3]
        · have h2' : a < t₂ := by linarith [not_le.mp h2]
          have h3 : (t₁ ≤ a ∧ a < t₂) := ⟨h1, h2'⟩
          simp [h1, h2, h3]
      · have hn2 : ¬ t₂ ≤ a := by have := not_le.mp h1; linarith
        have hn3 : ¬ (t₁ ≤ a ∧ a < t₂) := by rintro ⟨hle, _⟩; exact h1 hle
        simp [h1, hn2, hn3]
    omega

/-- The crossing counts of the two sub-rays differ by the number of crossing parameters lying in
the half-open window `[t₁,t₂)`. -/
lemma subRay_count_window {rr : Ray} {t₁ t₂ : ℚ} (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂)
    {poly : Polygon} (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hav : rayAvoidsVertices rr poly) :
    intersectionRayPolygonSegmentsNumber (subRay rr t₁) poly
      = intersectionRayPolygonSegmentsNumber (subRay rr t₂) poly
        + (crossParams rr poly).countP (fun u => decide (t₁ ≤ u ∧ u < t₂)) := by
  have ht2 : 0 ≤ t₂ := le_trans ht1 ht12
  rw [intersection_subRay_eq_countP rr poly ht1 hnd hav,
      intersection_subRay_eq_countP rr poly ht2 hnd hav,
      ← countP_beyond_eq rr poly t₁, ← countP_beyond_eq rr poly t₂]
  exact countP_ge_split (crossParams rr poly) ht12

/-- **One-crossing flip (sub-ray form).** If `rr` avoids `poly`'s vertices, both sub-ray origins
are off `poly`'s boundary, and exactly one crossing parameter lies in the window `[t₁,t₂)`, then
the two sub-ray origins have *opposite* `poly.interior` status. -/
lemma flip_subRay_one {rr : Ray} {t₁ t₂ : ℚ} (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂)
    {poly : Polygon} (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hav : rayAvoidsVertices rr poly)
    (hoff1 : ∀ seg ∈ poly.segments, (subRay rr t₁).origin ∉ seg.toSet)
    (hoff2 : ∀ seg ∈ poly.segments, (subRay rr t₂).origin ∉ seg.toSet)
    (hwin : (crossParams rr poly).countP (fun u => decide (t₁ ≤ u ∧ u < t₂)) = 1) :
    ((subRay rr t₁).origin ∈ poly.interior ↔ (subRay rr t₂).origin ∉ poly.interior) := by
  have ht2 : 0 ≤ t₂ := le_trans ht1 ht12
  have hcount := subRay_count_window ht1 ht12 hnd hav
  rw [hwin] at hcount
  rw [mem_interior_iff_subRay poly rr ht1 hnd hav hoff1,
      mem_interior_iff_subRay poly rr ht2 hnd hav hoff2]
  omega

/-! ## Parallel perturbation off the line `PQ`.

We translate the whole segment `[P,Q]` by `k·n`, where `n = (Q.y-P.y, -(Q.x-P.x))` is
perpendicular to `Q-P`.  The endpoints become `Psh = P + k·n`, `Qsh = Q + k·n`.  The two
connecting legs `[P,Psh]` and `[Qsh,Q]` are short (length `≤ k·Mrat`), so for small `k` they
miss `poly`'s boundary; `even_odd_constancy` then transfers interior status. -/

/-- The parallel-shifted point of `v` by `k·n`. -/
def Psh (P Q v : Vector2D) (k : ℚ) : Vector2D :=
  ⟨v.x + k*(Q.y-P.y), v.y - k*(Q.x-P.x)⟩

lemma vR_Psh (P Q v : Vector2D) (k : ℚ) :
    vR (Psh P Q v k) = ((vR v).1 + (k:ℝ)*(perpR (vR P) (vR Q)).1,
                        (vR v).2 + (k:ℝ)*(perpR (vR P) (vR Q)).2) := by
  unfold vR Psh perpR
  ext
  · show ((((v.x) + k*(Q.y-P.y)):ℚ):ℝ) = _
    push_cast; ring
  · show ((((v.y) - k*(Q.x-P.x)):ℚ):ℝ) = _
    push_cast; ring

/-- Real closeness of the leg `[v, Psh v]` to the single point `vR v`. -/
lemma legPsh_close (P Q v : Vector2D) (k : ℝ) (hk : 0 ≤ k) :
    ∀ s ∈ Icc (0:ℝ) 1,
      dist (segR (vR v) (((vR v).1 + k*(perpR (vR P) (vR Q)).1,
                          (vR v).2 + k*(perpR (vR P) (vR Q)).2)) s)
           (vR v) ≤ k * max |(perpR (vR P) (vR Q)).1| |(perpR (vR P) (vR Q)).2| := by
  intro s hs
  set p := vR P; set q := vR Q
  have heq : segR (vR v) ((vR v).1 + k*(perpR p q).1, (vR v).2 + k*(perpR p q).2) s
      = ((vR v).1 + (s*k)*(perpR p q).1, (vR v).2 + (s*k)*(perpR p q).2) := by
    unfold segR
    ext <;> (simp only; ring)
  rw [heq]
  refine le_trans (dist_shift (vR v) ((s*k)*(perpR p q).1) ((s*k)*(perpR p q).2)) ?_
  have hsk : |s*k| ≤ k := by
    rw [abs_mul, abs_of_nonneg hs.1, abs_of_nonneg hk]; nlinarith [hs.2, hk]
  apply max_le
  · rw [abs_mul]
    calc |s*k| * |(perpR p q).1| ≤ k * |(perpR p q).1| :=
          mul_le_mul_of_nonneg_right hsk (abs_nonneg _)
       _ ≤ k * max |(perpR p q).1| |(perpR p q).2| :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hk
  · rw [abs_mul]
    calc |s*k| * |(perpR p q).2| ≤ k * |(perpR p q).2| :=
          mul_le_mul_of_nonneg_right hsk (abs_nonneg _)
       _ ≤ k * max |(perpR p q).1| |(perpR p q).2| :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hk

/-- A point `v` not on an edge `[a,b]` has its short parallel leg `[v, Psh v]` miss `[a,b]` for
small `k`. -/
lemma legPt_edge_bf (P Q : Vector2D) (v a b : Vector2D) (hab : a ≠ b)
    (hvP : ∃ sv : ℝ, sv ∈ Icc (0:ℝ) 1 ∧ vR v = segR (vR P) (vR Q) sv)
    (hv_off : v ∉ (LineSegment.mk a b).toSet) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ w : Vector2D, w ∈ (LineSegment.mk v (Psh P Q v k)).toSet →
        w ∉ (LineSegment.mk a b).toSet := by
  obtain ⟨sv, hsv, hvR⟩ := hvP
  -- real disjointness of the constant segment {vR v} from [a,b]
  have hdisj : ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1,
      segR (vR v) (vR v) s ≠ segR (vR a) (vR b) u := by
    intro s _ u hu heq
    apply hv_off
    -- segR v v s = vR v;  equals segR a b u ⇒ v ∈ [a,b]
    obtain ⟨hu0, hu1⟩ := hu
    have hvx : (vR v).1 = (1-u)*(vR a).1 + u*(vR b).1 := by
      have h := congrArg Prod.fst heq; simp only [segR] at h
      rw [show (1-s)*(vR v).1 + s*(vR v).1 = (vR v).1 from by ring] at h; exact h
    have hvy : (vR v).2 = (1-u)*(vR a).2 + u*(vR b).2 := by
      have h := congrArg Prod.snd heq; simp only [segR] at h
      rw [show (1-s)*(vR v).2 + s*(vR v).2 = (vR v).2 from by ring] at h; exact h
    -- real coordinate equations on the casts
    have hvx' : (v.x:ℝ) = (1-u)*(a.x:ℝ) + u*(b.x:ℝ) := by simpa [vR] using hvx
    have hvy' : (v.y:ℝ) = (1-u)*(a.y:ℝ) + u*(b.y:ℝ) := by simpa [vR] using hvy
    -- the line/collinearity condition holds over ℝ, hence over ℚ
    have hlineR : ((b.x:ℝ)-a.x)*((v.y:ℝ)-a.y) - ((b.y:ℝ)-a.y)*((v.x:ℝ)-a.x) = 0 := by
      have e1 : (v.x:ℝ) - a.x = u*((b.x:ℝ)-a.x) := by rw [hvx']; ring
      have e2 : (v.y:ℝ) - a.y = u*((b.y:ℝ)-a.y) := by rw [hvy']; ring
      rw [e1, e2]; ring
    have hlineQ : (b.x-a.x)*(v.y-a.y) - (b.y-a.y)*(v.x-a.x) = 0 := by
      have : (((b.x-a.x)*(v.y-a.y) - (b.y-a.y)*(v.x-a.x):ℚ):ℝ) = 0 := by push_cast; linarith [hlineR]
      exact_mod_cast this
    -- decide which coordinate of [a,b] is nondegenerate
    rcases eq_or_ne (b.x) (a.x) with hbx | hbx
    · -- b.x = a.x, so b.y ≠ a.y
      have hby : b.y ≠ a.y := by
        intro h; exact hab (by ext <;> [exact hbx.symm; exact h.symm])
      have hdy : b.y - a.y ≠ 0 := sub_ne_zero.mpr hby
      have hu_eq : u = ((v.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := by
        have hdyR : (b.y:ℝ) - a.y ≠ 0 := by
          intro h; apply hdy; have : ((b.y - a.y:ℚ):ℝ) = 0 := by push_cast; linarith
          exact_mod_cast this
        rw [eq_div_iff hdyR]; rw [hvy']; ring
      have hu0 : (0:ℚ) ≤ (v.y-a.y)/(b.y-a.y) := by
        have : (0:ℝ) ≤ ((v.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := hu_eq ▸ hu0
        have e : (((v.y-a.y)/(b.y-a.y):ℚ):ℝ) = ((v.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := by push_cast; ring
        rw [← e] at this; exact_mod_cast this
      have hu1 : (v.y-a.y)/(b.y-a.y) ≤ 1 := by
        have : ((v.y:ℝ)-a.y)/((b.y:ℝ)-a.y) ≤ 1 := hu_eq ▸ hu1
        have e : (((v.y-a.y)/(b.y-a.y):ℚ):ℝ) = ((v.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := by push_cast; ring
        rw [← e] at this; exact_mod_cast this
      exact mem_seg_of_y hlineQ hdy ⟨hu0, hu1⟩
    · have hdx : b.x - a.x ≠ 0 := sub_ne_zero.mpr hbx
      have hu_eq : u = ((v.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := by
        have hdxR : (b.x:ℝ) - a.x ≠ 0 := by
          intro h; apply hdx; have : ((b.x - a.x:ℚ):ℝ) = 0 := by push_cast; linarith
          exact_mod_cast this
        rw [eq_div_iff hdxR]; rw [hvx']; ring
      have hu0 : (0:ℚ) ≤ (v.x-a.x)/(b.x-a.x) := by
        have : (0:ℝ) ≤ ((v.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := hu_eq ▸ hu0
        have e : (((v.x-a.x)/(b.x-a.x):ℚ):ℝ) = ((v.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := by push_cast; ring
        rw [← e] at this; exact_mod_cast this
      have hu1 : (v.x-a.x)/(b.x-a.x) ≤ 1 := by
        have : ((v.x:ℝ)-a.x)/((b.x:ℝ)-a.x) ≤ 1 := hu_eq ▸ hu1
        have e : (((v.x-a.x)/(b.x-a.x):ℚ):ℝ) = ((v.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := by push_cast; ring
        rw [← e] at this; exact_mod_cast this
      exact mem_seg_of_x hlineQ hdx ⟨hu0, hu1⟩
  obtain ⟨δ, hδ, hsep⟩ := seg_sep (vR v) (vR v) (vR a) (vR b) hdisj
  obtain ⟨c, hc0, hcδ⟩ := exists_rat_btwn hδ
  have hc0' : 0 < c := by exact_mod_cast hc0
  set M : ℚ := max |Q.y - P.y| |Q.x - P.x| with hM
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  set ε : ℚ := c / (M + 1) with hε
  have hMpos : (0:ℚ) < M + 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  refine ⟨ε, hε0, ?_⟩
  intro k hk0 hkε w hw hwab
  -- w on leg ⇒ vR w = segR (vR v) (shifted) s
  obtain ⟨t, ht, hwt⟩ := vR_mem_seg hw
  have hkR : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast le_of_lt hk0
  have hperpM : max |(perpR (vR P) (vR Q)).1| |(perpR (vR P) (vR Q)).2| = ((M:ℚ):ℝ) := by
    rw [hM]; exact perp_norm_eq P Q
  have hcl := legPsh_close P Q v (k:ℝ) hkR t ht
  rw [hperpM] at hcl
  -- w as point of [a,b]
  obtain ⟨ub, hub0, hub1, hwax, hway⟩ := hwab
  have hwe : vR w = segR (vR a) (vR b) (ub:ℝ) := by
    unfold vR segR; ext
    · push_cast [hwax]; ring
    · push_cast [hway]; ring
  have hube : (ub:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by exact_mod_cast hub0, by exact_mod_cast hub1⟩
  -- the real leg point equals vR w; rewrite hwt to match legPsh_close's segR
  have hwt' : vR w = segR (vR v) (((vR v).1 + (k:ℝ)*(perpR (vR P) (vR Q)).1,
                       (vR v).2 + (k:ℝ)*(perpR (vR P) (vR Q)).2)) t := by
    rw [hwt, vR_Psh]
  have hρlt : (k:ℝ) * ((M:ℚ):ℝ) < δ := by
    have hkMle : k * M ≤ ε * M := mul_le_mul_of_nonneg_right hkε hMnn
    have hεM : ε * M ≤ c := by
      rw [hε, div_mul_eq_mul_div, div_le_iff₀ hMpos]; nlinarith [hMnn, hc0']
    have : (k:ℝ) * ((M:ℚ):ℝ) ≤ ((c:ℚ):ℝ) := by
      have h := le_trans hkMle hεM
      calc (k:ℝ) * ((M:ℚ):ℝ) = (((k*M:ℚ)):ℝ) := by push_cast; ring
        _ ≤ ((c:ℚ):ℝ) := by exact_mod_cast h
    linarith [this, hcδ]
  -- separation gives δ ≤ dist (vR v) (segR a b ub)
  have hsepP : δ ≤ dist (vR v) (segR (vR a) (vR b) (ub:ℝ)) := by
    have := hsep 0 (by constructor <;> norm_num) ub hube
    have hvv : segR (vR v) (vR v) (0:ℝ) = vR v := by simp only [segR]; ext <;> ring
    rw [hvv] at this; exact this
  -- the leg point equals segR a b ub
  have heqpt : segR (vR v) (((vR v).1 + (k:ℝ)*(perpR (vR P) (vR Q)).1,
                  (vR v).2 + (k:ℝ)*(perpR (vR P) (vR Q)).2)) t = segR (vR a) (vR b) (ub:ℝ) := by
    rw [← hwt', hwe]
  -- triangle: dist(vR v, segR a b ub) ≤ dist(vR v, legpt) + 0
  have htri : dist (vR v) (segR (vR a) (vR b) (ub:ℝ))
      ≤ dist (vR v) (segR (vR v) (((vR v).1 + (k:ℝ)*(perpR (vR P) (vR Q)).1,
                  (vR v).2 + (k:ℝ)*(perpR (vR P) (vR Q)).2)) t) := by rw [heqpt]
  rw [dist_comm] at hcl
  linarith [le_trans hsepP htri, hcl, hρlt]

/-- The whole parallel leg `[v, Psh v]` misses `poly`'s boundary for small `k`, when `v` is off
the boundary and lies on the line `[P,Q]`. -/
lemma legPt_bf (P Q : Vector2D) (v : Vector2D) (poly : Polygon)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hvP : ∃ sv : ℝ, sv ∈ Icc (0:ℝ) 1 ∧ vR v = segR (vR P) (vR Q) sv)
    (hv_off : v ∉ poly.toBoundarySet) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ w : Vector2D, w ∈ (LineSegment.mk v (Psh P Q v k)).toSet → w ∉ poly.toBoundarySet := by
  have hedge : ∀ e ∈ poly.segments, ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ w : Vector2D, w ∈ (LineSegment.mk v (Psh P Q v k)).toSet → w ∉ e.toSet := by
    intro e he
    obtain ⟨a, b⟩ := e
    have hab : a ≠ b := hnd ⟨a,b⟩ he
    have hvoff_e : v ∉ (LineSegment.mk a b).toSet := by
      intro hb; exact hv_off ⟨⟨a,b⟩, he, hb⟩
    exact legPt_edge_bf P Q v a b hab hvP hvoff_e
  obtain ⟨ε, hε, hgood⟩ := exists_uniform_eps poly.segments
    (fun e ε => ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ w : Vector2D, w ∈ (LineSegment.mk v (Psh P Q v k)).toSet → w ∉ e.toSet)
    (fun e ε ε' hε' hle hg k hk0 hkε w hw => hg k hk0 (le_trans hkε hle) w hw)
    hedge
  refine ⟨ε, hε, ?_⟩
  intro k hk0 hkε w hw hwb
  obtain ⟨e, he, hwe⟩ := hwb
  exact hgood e he k hk0 hkε w hw hwe

end Polygons2
end
