import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.Interior
import Polygons2.Constancy
import Polygons2.ClipM
import Polygons2.ClipProps
import Polygons2.AcapBA

/-!
# Corner lemma (variant `_C`): an endpoint reached through the interior is not a
double-boundary point.

This proves `endpoint_off_double_C`, the last gap of the polygon-intersection development.

The proof is **rate-free**: rather than balancing a perpendicular-shift size against an interior
radius, we localise to a small ball `B(q,ρ)` chosen so small that it meets only those `Mlist`
edges that actually contain `q`.  We then produce
* a leg point `v ∈ poly1.interior ∩ poly2.interior` close to `q` (off `∂poly1 ∩ ∂poly2`), and
* a point `z` on the `poly1`-edge through `q` close to `q`, off `∂poly2`,
with the short segment `[v,z]` staying inside `B(q,ρ)` and avoiding `∂poly1 ∩ ∂poly2`.

If `[v,z]` avoided every `Mlist`-edge, `main_dir` would force `z ∈ poly1.interior`, contradicting
`z ∈ ∂poly1`.  Hence `[v,z]` meets some `Mlist`-edge `e0`; but `[v,z] ⊆ B(q,ρ)` forces `e0` to
contain a point of `B(q,ρ)`, hence (by the choice of `ρ`) `q ∈ e0`.  As `q ∈ [p,q]` this
contradicts the hypothesis that `[p,q]` avoids `Mlist`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-! ## Real-analysis helpers -/

/-- `vR (segPt a b t) = segR (vR a) (vR b) t`. -/
lemma vR_segPt (a b : Vector2D) (t : ℚ) :
    vR (segPt a b t) = segR (vR a) (vR b) (t:ℝ) := by
  unfold vR segPt segR; ext
  · push_cast; ring
  · push_cast; ring

/-- A rational point whose real image lies on the real segment `[a,b]` (with `a ≠ b`) lies on the
rational segment `[a,b]`. -/
lemma mem_rat_seg_of_real {a b w : Vector2D} (hab : a ≠ b)
    (h : ∃ u ∈ Icc (0:ℝ) 1, vR w = segR (vR a) (vR b) u) :
    w ∈ (LineSegment.mk a b).toSet := by
  obtain ⟨u, hu, hwu⟩ := h
  obtain ⟨hu0, hu1⟩ := hu
  have hx : (w.x:ℝ) = (1-u)*(a.x:ℝ) + u*(b.x:ℝ) := by
    have := congrArg Prod.fst hwu; simpa [segR, vR] using this
  have hy : (w.y:ℝ) = (1-u)*(a.y:ℝ) + u*(b.y:ℝ) := by
    have := congrArg Prod.snd hwu; simpa [segR, vR] using this
  have hlineR : ((b.x:ℝ)-a.x)*((w.y:ℝ)-a.y) - ((b.y:ℝ)-a.y)*((w.x:ℝ)-a.x) = 0 := by
    have e1 : (w.x:ℝ) - a.x = u*((b.x:ℝ)-a.x) := by rw [hx]; ring
    have e2 : (w.y:ℝ) - a.y = u*((b.y:ℝ)-a.y) := by rw [hy]; ring
    rw [e1, e2]; ring
  have hlineQ : (b.x-a.x)*(w.y-a.y) - (b.y-a.y)*(w.x-a.x) = 0 := by
    have : (((b.x-a.x)*(w.y-a.y) - (b.y-a.y)*(w.x-a.x):ℚ):ℝ) = 0 := by push_cast; linarith [hlineR]
    exact_mod_cast this
  rcases eq_or_ne (b.x) (a.x) with hbx | hbx
  · have hby : b.y ≠ a.y := by
      intro hh; exact hab (by ext <;> [exact hbx.symm; exact hh.symm])
    have hdy : b.y - a.y ≠ 0 := sub_ne_zero.mpr hby
    have hdyR : (b.y:ℝ) - a.y ≠ 0 := by
      intro hh; apply hdy; have : ((b.y - a.y:ℚ):ℝ) = 0 := by push_cast; linarith
      exact_mod_cast this
    have hu_eq : u = ((w.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := by
      rw [eq_div_iff hdyR]; rw [hy]; ring
    have hq0 : (0:ℚ) ≤ (w.y-a.y)/(b.y-a.y) := by
      have hge : (0:ℝ) ≤ ((w.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := hu_eq ▸ hu0
      have e : (((w.y-a.y)/(b.y-a.y):ℚ):ℝ) = ((w.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := by push_cast; ring
      rw [← e] at hge; exact_mod_cast hge
    have hq1 : (w.y-a.y)/(b.y-a.y) ≤ 1 := by
      have hle : ((w.y:ℝ)-a.y)/((b.y:ℝ)-a.y) ≤ 1 := hu_eq ▸ hu1
      have e : (((w.y-a.y)/(b.y-a.y):ℚ):ℝ) = ((w.y:ℝ)-a.y)/((b.y:ℝ)-a.y) := by push_cast; ring
      rw [← e] at hle; exact_mod_cast hle
    exact mem_seg_of_y hlineQ hdy ⟨hq0, hq1⟩
  · have hdx : b.x - a.x ≠ 0 := sub_ne_zero.mpr hbx
    have hdxR : (b.x:ℝ) - a.x ≠ 0 := by
      intro hh; apply hdx; have : ((b.x - a.x:ℚ):ℝ) = 0 := by push_cast; linarith
      exact_mod_cast this
    have hu_eq : u = ((w.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := by
      rw [eq_div_iff hdxR]; rw [hx]; ring
    have hq0 : (0:ℚ) ≤ (w.x-a.x)/(b.x-a.x) := by
      have hge : (0:ℝ) ≤ ((w.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := hu_eq ▸ hu0
      have e : (((w.x-a.x)/(b.x-a.x):ℚ):ℝ) = ((w.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := by push_cast; ring
      rw [← e] at hge; exact_mod_cast hge
    have hq1 : (w.x-a.x)/(b.x-a.x) ≤ 1 := by
      have hle : ((w.x:ℝ)-a.x)/((b.x:ℝ)-a.x) ≤ 1 := hu_eq ▸ hu1
      have e : (((w.x-a.x)/(b.x-a.x):ℚ):ℝ) = ((w.x:ℝ)-a.x)/((b.x:ℝ)-a.x) := by push_cast; ring
      rw [← e] at hle; exact_mod_cast hle
    exact mem_seg_of_x hlineQ hdx ⟨hq0, hq1⟩

/-! ## Distance bounds: points near `q` -/

/-- The real-segment point `segR c d s` written as a convex combination. -/
lemma segR_eq_convex (c d : ℝ × ℝ) (s : ℝ) :
    segR c d s = (1-s) • c + s • d := by
  unfold segR
  ext <;> simp [Prod.smul_def]

/-- Every point of a real segment `[c,d]` whose endpoints are within `ρ` of `x` is within `ρ` of
`x` (convexity of the ball). -/
lemma segR_dist_le {c d x : ℝ × ℝ} {ρ : ℝ}
    (hc : dist c x ≤ ρ) (hd : dist d x ≤ ρ) :
    ∀ s ∈ Icc (0:ℝ) 1, dist (segR c d s) x ≤ ρ := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  rw [segR_eq_convex]
  -- x = (1-s)•x + s•x
  have hxeq : x = (1-s) • x + s • x := by
    rw [← add_smul]; norm_num
  calc dist ((1-s) • c + s • d) x
      = dist ((1-s) • c + s • d) ((1-s) • x + s • x) := by rw [← hxeq]
    _ ≤ ρ := by
        rw [dist_eq_norm]
        have : (1-s) • c + s • d - ((1-s) • x + s • x)
            = (1-s) • (c - x) + s • (d - x) := by
          rw [smul_sub, smul_sub]; abel
        rw [this]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1-s), abs_of_nonneg hs0]
        have hcx : ‖c - x‖ ≤ ρ := by rw [← dist_eq_norm]; exact hc
        have hdx : ‖d - x‖ ≤ ρ := by rw [← dist_eq_norm]; exact hd
        nlinarith [mul_le_mul_of_nonneg_left hcx (by linarith : (0:ℝ) ≤ 1-s),
          mul_le_mul_of_nonneg_left hdx hs0]

/-! ## Separation of `q` from a segment it is not on -/

/-- If `q` is not on the rational segment `[a,b]`, then `vR q` is bounded away from the real
segment `[a,b]`. -/
lemma sep_of_not_mem {a b q : Vector2D} (hab : a ≠ b) (hq : q ∉ (LineSegment.mk a b).toSet) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (0:ℝ) 1, δ ≤ dist (vR q) (segR (vR a) (vR b) s) := by
  have hdisj : ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1,
      segR (vR q) (vR q) s ≠ segR (vR a) (vR b) u := by
    intro s _ u hu heq
    apply hq
    apply mem_rat_seg_of_real hab
    refine ⟨u, hu, ?_⟩
    rw [← heq]; unfold segR; ext <;> (simp only; ring)
  obtain ⟨δ, hδ, hsep⟩ := seg_sep (vR q) (vR q) (vR a) (vR b) hdisj
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have := hsep 0 ⟨le_refl _, by norm_num⟩ s hs
  have hqq : segR (vR q) (vR q) (0:ℝ) = vR q := by unfold segR; ext <;> (simp only; ring)
  rw [hqq] at this; exact this

/-- A rational segment `[c,d]` all of whose points are strictly within `δ` of `q` (in the real
embedding) misses `[a,b]`, provided `q` is `δ`-separated from `[a,b]`. -/
lemma seg_avoids_of_close {a b c d q : Vector2D} {δ : ℝ}
    (hsep : ∀ s ∈ Icc (0:ℝ) 1, δ ≤ dist (vR q) (segR (vR a) (vR b) s))
    (hcd : ∀ s ∈ Icc (0:ℝ) 1, dist (segR (vR c) (vR d) s) (vR q) < δ) :
    ∀ w ∈ (LineSegment.mk c d).toSet, w ∉ (LineSegment.mk a b).toSet := by
  intro w hw hwab
  -- w on [c,d] gives a real param
  obtain ⟨t, ht, hwt⟩ := vR_mem_seg hw
  -- w on [a,b] gives a real param
  obtain ⟨u, hu, hwu⟩ := vR_mem_seg hwab
  have hclose := hcd t ht
  have hsepu := hsep u hu
  -- segR c d t = vR w = segR a b u
  have heq : segR (vR c) (vR d) t = segR (vR a) (vR b) u := by rw [← hwt, ← hwu]
  rw [heq, dist_comm] at hclose
  linarith

/-! ## Distance of `segPt`-points to an endpoint -/

/-- `dist (vR (segPt a b t)) (vR b) = |1-t| · dist (vR a) (vR b)`. -/
lemma dist_segPt_right (a b : Vector2D) (t : ℚ) :
    dist (vR (segPt a b t)) (vR b) = |1 - (t:ℝ)| * dist (vR a) (vR b) := by
  rw [vR_segPt]
  -- segR a b t - b = (1-t)(a - b)
  rw [dist_eq_norm, dist_eq_norm]
  have hid : segR (vR a) (vR b) (t:ℝ) - vR b = (1 - (t:ℝ)) • (vR a - vR b) := by
    rw [segR_eq_convex]; module
  rw [hid, norm_smul, Real.norm_eq_abs]

/-- `dist (vR (segPt a b t)) (vR a) = |t| · dist (vR a) (vR b)`. -/
lemma dist_segPt_left (a b : Vector2D) (t : ℚ) :
    dist (vR (segPt a b t)) (vR a) = |(t:ℝ)| * dist (vR a) (vR b) := by
  rw [vR_segPt]
  rw [dist_eq_norm, dist_eq_norm]
  have hid : segR (vR a) (vR b) (t:ℝ) - vR a = (t:ℝ) • (vR b - vR a) := by
    rw [segR_eq_convex]; module
  rw [hid, norm_smul, Real.norm_eq_abs, norm_sub_rev (vR b) (vR a)]

/-! ## The prefix `[p, segPt p q t]` lies inside `[p,q]` -/

/-- `[p, segPt p q t].toSet ⊆ [p,q].toSet` for `t ∈ [0,1]`. -/
lemma prefix_subset {p q : Vector2D} {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (LineSegment.mk p (segPt p q t)).toSet ⊆ (LineSegment.mk p q).toSet := by
  rintro x ⟨w, hw0, hw1, hx, hy⟩
  refine ⟨w * t, mul_nonneg hw0 ht0, ?_, ?_, ?_⟩
  · nlinarith [hw0, hw1, ht0, ht1]
  · rw [hx]; simp only [segPt_x]; ring
  · rw [hy]; simp only [segPt_y]; ring

/-! ## Choosing a parameter avoiding a finite bad set, close to `1` -/

/-- Given a finite set `Bad ⊆ ℚ` and `ε > 0`, there is `t ∈ (1-ε, 1)` with `t ∉ Bad`. -/
lemma exists_param_near_one (Bad : Finset ℚ) {ε : ℚ} (hε : 0 < ε) :
    ∃ t : ℚ, 1 - ε < t ∧ t < 1 ∧ t ∉ Bad := by
  have hlt : (1 - ε) < (1:ℚ) := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℚ, t ∈ (Set.Ioo (1-ε) (1:ℚ)) \ (Bad : Set ℚ) :=
    ((Set.Ioo_infinite hlt).diff Bad.finite_toSet).nonempty
  obtain ⟨⟨h1, h2⟩, h3⟩ := ht
  exact ⟨t, h1, h2, by simpa using h3⟩

/-- Given a finite set `Bad ⊆ ℚ` and `ε > 0`, there is `t ∈ (uq, uq+ε)` with `t ∉ Bad`,
for any `uq`. -/
lemma exists_param_near (Bad : Finset ℚ) (uq : ℚ) {ε : ℚ} (hε : 0 < ε) :
    ∃ t : ℚ, uq < t ∧ t < uq + ε ∧ t ∉ Bad := by
  have hlt : uq < uq + ε := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℚ, t ∈ (Set.Ioo uq (uq+ε)) \ (Bad : Set ℚ) :=
    ((Set.Ioo_infinite hlt).diff Bad.finite_toSet).nonempty
  obtain ⟨⟨h1, h2⟩, h3⟩ := ht
  exact ⟨t, h1, h2, by simpa using h3⟩

/-! ## A leg point in the interior, close to `q`, off the double boundary -/

/-- There is a leg point `v = segPt p q t` (with `t ∈ (0,1)`), in `poly1.interior ∩
poly2.interior`, off `∂poly1 ∩ ∂poly2`, with `dist (vR v) (vR q) < ρ`. -/
lemma exists_leg_point (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p q : Vector2D} (hpne : p ≠ q)
    (hpq : ∀ x ∈ (LineSegment.mk p q).toSet, ∀ e ∈ Mlist poly1 poly2,
        x ∉ (LineSegment.mk e.1 e.2).toSet)
    (hp1 : p ∈ poly1.interior) (hp2 : p ∈ poly2.interior)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ v : Vector2D, v ∈ poly1.interior ∧ v ∈ poly2.interior ∧
      v ∉ poly1.toBoundarySet ∩ poly2.toBoundarySet ∧
      dist (vR v) (vR q) < ρ := by
  -- the finite bad set of parameters
  have hpre : Set.Finite ((segPt p q) ⁻¹' (poly1.toBoundarySet ∩ poly2.toBoundarySet)) := by
    apply hfin.preimage
    intro s _ t _ h
    exact segPt_injOn hpne h
  set Bad : Finset ℚ := hpre.toFinset with hBad
  -- distance factor
  set D : ℝ := dist (vR p) (vR q) with hD
  have hD0 : 0 ≤ D := dist_nonneg
  -- pick ε
  obtain ⟨ε, hε0, hεle1, hεrho⟩ : ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 ∧ (ε:ℝ) * D < ρ := by
    obtain ⟨ε0, hε00, hεlt⟩ := exists_pos_rat_lt (show (0:ℝ) < ρ / (D + 1) from by positivity)
    refine ⟨min ε0 1, lt_min hε00 one_pos, min_le_right _ _, ?_⟩
    have hεR : (ε0:ℝ) < ρ / (D+1) := hεlt
    rw [lt_div_iff₀ (by positivity)] at hεR
    have hmin : ((min ε0 1 : ℚ):ℝ) ≤ (ε0:ℝ) := by exact_mod_cast min_le_left _ _
    have hmin0 : (0:ℝ) ≤ ((min ε0 1 : ℚ):ℝ) := by exact_mod_cast (lt_min hε00 one_pos).le
    nlinarith [hεR, hD0, hmin, hmin0]
  obtain ⟨t, ht1, ht2, htBad⟩ := exists_param_near_one Bad hε0
  -- bounds on t
  have ht0 : 0 < t := by
    have : (1:ℚ) - ε < t := ht1; linarith [hεle1]
  have ht1' : t < 1 := ht2
  set v := segPt p q t with hv
  have hvnotbad : v ∉ poly1.toBoundarySet ∩ poly2.toBoundarySet := by
    intro hb
    apply htBad
    rw [hBad, Set.Finite.mem_toFinset]
    exact hb
  -- [p,v] avoids M
  have hpqv : ∀ x ∈ (LineSegment.mk p v).toSet, ∀ e ∈ Mlist poly1 poly2,
      x ∉ (LineSegment.mk e.1 e.2).toSet := by
    intro x hx e he
    exact hpq x (prefix_subset ht0.le ht1'.le hx) e he
  -- main_dir gives v ∈ int1 ∩ int2
  obtain ⟨hv1, hv2⟩ := main_dir poly1 poly2 h1n h2n h1e h2e hfin hpqv hvnotbad hp1 hp2
  refine ⟨v, hv1, hv2, hvnotbad, ?_⟩
  -- distance bound
  rw [hv, dist_segPt_right]
  have htR1 : (t:ℝ) ≤ 1 := by exact_mod_cast ht1'.le
  have habs : |1 - (t:ℝ)| = 1 - (t:ℝ) := by
    rw [abs_of_nonneg]; linarith
  rw [habs]
  have h1t : (1:ℝ) - (t:ℝ) < (ε:ℝ) := by
    have : (1:ℝ) - ε < t := by exact_mod_cast ht1
    linarith
  calc (1 - (t:ℝ)) * D ≤ (ε:ℝ) * D := by
        apply mul_le_mul_of_nonneg_right (le_of_lt h1t) hD0
    _ < ρ := hεrho

/-! ## A point on the `poly1`-edge through `q`, off `∂poly2`, close to `q` -/

/-- The cut set of edge `⟨a,b⟩` against `poly2` is finite (here `q` lies on the edge and the edge
is a `poly1`-edge), so its cut-parameter `Finset` collects all `u ∈ [0,1]` with
`segPt a b u ∈ ∂poly2`. -/
lemma cutFinset_eq {a b : Vector2D} (hab : a ≠ b) {poly1 poly2 : Polygon}
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {u : ℚ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hb : segPt a b u ∈ poly2.toBoundarySet) :
    u ∈ cutFinset a b poly2 := by
  have hfinSet : Set.Finite (cutSet a b poly2) := cutSet_finite hab hsub hfin
  unfold cutFinset
  rw [dif_pos hfinSet, Set.Finite.mem_toFinset]
  exact ⟨hu0, hu1, hb⟩

/-- There is a point `z = segPt a b u` (with `u ∈ [0,1]`) on the `poly1`-edge `⟨a,b⟩` through
`q = segPt a b uq`, off `∂poly2`, with `dist (vR z) (vR q) < ρ`. -/
lemma exists_edge_point {a b q : Vector2D} (hab : a ≠ b)
    {poly1 poly2 : Polygon}
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {uq : ℚ} (huq0 : 0 ≤ uq) (huq1 : uq ≤ 1) (hq : q = segPt a b uq)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z : Vector2D, z ∈ (LineSegment.mk a b).toSet ∧ z ∉ poly2.toBoundarySet ∧
      dist (vR z) (vR q) < ρ := by
  set D : ℝ := dist (vR a) (vR b) with hD
  have hD0 : 0 < D := by
    rw [hD, dist_pos]
    intro h
    apply hab
    -- vR a = vR b ⇒ a = b
    have hx : (a.x:ℝ) = (b.x:ℝ) := congrArg Prod.fst h
    have hy : (a.y:ℝ) = (b.y:ℝ) := congrArg Prod.snd h
    ext <;> [exact_mod_cast hx; exact_mod_cast hy]
  -- pick ε > 0 with ε·D < ρ
  obtain ⟨ε, hε0, hεrho⟩ : ∃ ε : ℚ, 0 < ε ∧ (ε:ℝ) * D < ρ := by
    obtain ⟨ε, hε0, hεlt⟩ := exists_pos_rat_lt (show (0:ℝ) < ρ / D from by positivity)
    refine ⟨ε, hε0, ?_⟩
    rw [lt_div_iff₀ hD0] at hεlt; linarith [hεlt]
  -- the cut Finset as bad set
  set Bad : Finset ℚ := cutFinset a b poly2 with hBad
  -- choose u near uq on a side with room
  by_cases hside : uq < 1
  · -- right side (uq, uq + δ) with δ = min ε (1 - uq)
    set δ : ℚ := min ε (1 - uq) with hδ
    have hδ0 : 0 < δ := lt_min hε0 (by linarith)
    obtain ⟨u, hu1lt, hu2lt, huBad⟩ := exists_param_near Bad uq hδ0
    have hu0 : 0 ≤ u := le_trans huq0 (le_of_lt hu1lt)
    have hule1 : u ≤ 1 := by
      have : u < uq + δ := hu2lt
      have hδle : δ ≤ 1 - uq := min_le_right _ _
      linarith
    have hzoff : segPt a b u ∉ poly2.toBoundarySet := by
      intro hb
      exact huBad (cutFinset_eq hab hsub hfin hu0 hule1 hb)
    refine ⟨segPt a b u, segPt_mem_seg hu0 hule1, hzoff, ?_⟩
    rw [hq, vR_segPt, vR_segPt]
    -- dist (segR a b u) (segR a b uq) = |u - uq| · D
    have hid : segR (vR a) (vR b) (u:ℝ) - segR (vR a) (vR b) (uq:ℝ)
        = ((u:ℝ) - uq) • (vR b - vR a) := by
      rw [segR_eq_convex, segR_eq_convex]; module
    rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs]
    have hdle : δ ≤ ε := min_le_left _ _
    have habs : |(u:ℝ) - uq| < (ε:ℝ) := by
      rw [abs_of_pos (by have : uq < u := hu1lt; exact_mod_cast (by linarith : (0:ℚ) < u - uq))]
      have : (u:ℝ) < uq + δ := by exact_mod_cast hu2lt
      have hdleR : (δ:ℝ) ≤ ε := by exact_mod_cast hdle
      linarith
    calc |(u:ℝ) - uq| * ‖vR b - vR a‖ < (ε:ℝ) * D := by
          rw [show ‖vR b - vR a‖ = D from by rw [hD, dist_eq_norm, norm_sub_rev]]
          apply mul_lt_mul_of_pos_right habs hD0
      _ < ρ := hεrho
  · -- uq = 1, use left side (uq - δ, uq)
    have hside' : 1 ≤ uq := not_lt.mp hside
    have huq1' : uq = 1 := le_antisymm huq1 hside'
    set δ : ℚ := min ε 1 with hδ
    have hδ0 : 0 < δ := lt_min hε0 one_pos
    obtain ⟨u, hu1lt, hu2lt, huBad⟩ := exists_param_near Bad (uq - δ) hδ0
    have hu0 : 0 ≤ u := by
      have : uq - δ < u := hu1lt
      have hδle1 : δ ≤ 1 := min_le_right _ _
      have : uq - 1 ≤ uq - δ := by linarith
      have : (0:ℚ) ≤ uq - δ := by rw [huq1']; linarith [min_le_right ε (1:ℚ)]
      linarith [hu1lt]
    have hule1 : u ≤ 1 := by
      have : u < uq - δ + δ := hu2lt
      have : u < uq := by linarith
      linarith [huq1']
    have hzoff : segPt a b u ∉ poly2.toBoundarySet := by
      intro hb
      exact huBad (cutFinset_eq hab hsub hfin hu0 hule1 hb)
    refine ⟨segPt a b u, segPt_mem_seg hu0 hule1, hzoff, ?_⟩
    rw [hq, vR_segPt, vR_segPt]
    have hid : segR (vR a) (vR b) (u:ℝ) - segR (vR a) (vR b) (uq:ℝ)
        = ((u:ℝ) - uq) • (vR b - vR a) := by
      rw [segR_eq_convex, segR_eq_convex]; module
    rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs]
    -- u < uq, so |u - uq| = uq - u < δ ≤ ε
    have hult : u < uq := by
      have : u < uq - δ + δ := hu2lt; linarith
    have habs : |(u:ℝ) - uq| < (ε:ℝ) := by
      rw [abs_of_neg (by exact_mod_cast (by linarith : (u:ℚ) - uq < 0))]
      have hlo : uq - δ < u := hu1lt
      have hdleR : (δ:ℝ) ≤ ε := by exact_mod_cast (min_le_left ε (1:ℚ))
      have : (uq:ℝ) - δ < u := by exact_mod_cast hlo
      linarith
    calc |(u:ℝ) - uq| * ‖vR b - vR a‖ < (ε:ℝ) * D := by
          rw [show ‖vR b - vR a‖ = D from by rw [hD, dist_eq_norm, norm_sub_rev]]
          apply mul_lt_mul_of_pos_right habs hD0
      _ < ρ := hεrho

/-! ## A separation radius isolating `q` from the `Mlist`-edges that avoid it -/

/-- For a finite list `L` of nondegenerate edges, there is `ρ > 0` such that any edge of `L`
either contains `q` or stays at distance `≥ ρ` from `q` (on its whole real segment). -/
lemma exists_sep_radius (L : List (Vector2D × Vector2D))
    (hnd : ∀ e ∈ L, e.1 ≠ e.2) (q : Vector2D) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ e ∈ L, q ∉ (LineSegment.mk e.1 e.2).toSet →
      ∀ s ∈ Icc (0:ℝ) 1, ρ ≤ dist (vR q) (segR (vR e.1) (vR e.2) s) := by
  induction L with
  | nil => exact ⟨1, one_pos, by intro e he; simp at he⟩
  | cons a t ih =>
    obtain ⟨ρt, hρt0, hρt⟩ := ih (fun e he => hnd e (List.mem_cons_of_mem a he))
    by_cases hqa : q ∈ (LineSegment.mk a.1 a.2).toSet
    · -- a contains q; the separation requirement for a is vacuous
      refine ⟨ρt, hρt0, ?_⟩
      intro e he hqe s hs
      rcases List.mem_cons.mp he with he1 | he2
      · subst he1; exact absurd hqa hqe
      · exact hρt e he2 hqe s hs
    · -- a does not contain q; separate
      obtain ⟨δa, hδa0, hδa⟩ := sep_of_not_mem (hnd a List.mem_cons_self) hqa
      refine ⟨min ρt δa, lt_min hρt0 hδa0, ?_⟩
      intro e he hqe s hs
      rcases List.mem_cons.mp he with he1 | he2
      · subst he1; exact le_trans (min_le_right _ _) (hδa s hs)
      · exact le_trans (min_le_left _ _) (hρt e he2 hqe s hs)

/-! ## The corner lemma -/

theorem endpoint_off_double_C (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p q : Vector2D}
    (hpq : ∀ x ∈ (LineSegment.mk p q).toSet, ∀ e ∈ Mlist poly1 poly2,
        x ∉ (LineSegment.mk e.1 e.2).toSet)
    (hp1 : p ∈ poly1.interior) (hp2 : p ∈ poly2.interior) :
    q ∉ poly1.toBoundarySet ∩ poly2.toBoundarySet := by
  rintro ⟨hqA, hqB⟩
  -- p ≠ q (else q = p ∈ interior, contradicting q ∈ ∂poly1)
  have hpne : p ≠ q := by
    rintro rfl; exact boundary_not_interior hqA hp1
  -- poly1-edge `e = ⟨a,b⟩` through `q`
  obtain ⟨e, he, hqe⟩ := hqA
  set a := e.p1 with ha
  set b := e.p2 with hb
  have hab : a ≠ b := h1n e he
  have hqe' : q ∈ (LineSegment.mk a b).toSet := by rw [ha, hb]; cases e; exact hqe
  have hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet := by
    intro x hx; exact ⟨e, he, by rw [ha, hb] at hx; cases e; exact hx⟩
  obtain ⟨uq, huq0, huq1, hquq⟩ := mem_seg_segPt hqe'
  -- separation radius isolating q from Mlist-edges that avoid it
  obtain ⟨ρ, hρ0, hρ⟩ :=
    exists_sep_radius (Mlist poly1 poly2) (Mlist_nondeg poly1 poly2) q
  -- a strictly smaller radius
  set ρ' : ℝ := ρ / 2 with hρ'
  have hρ'0 : 0 < ρ' := by rw [hρ']; linarith
  have hρ'lt : ρ' < ρ := by rw [hρ']; linarith
  -- leg point v near q
  obtain ⟨v, hv1, hv2, hvF, hvdist⟩ :=
    exists_leg_point poly1 poly2 h1n h2n h1e h2e hfin hpne hpq hp1 hp2 hρ'0
  -- edge point z near q
  obtain ⟨z, hzab, hzoff, hzdist⟩ :=
    exists_edge_point hab hsub hfin huq0 huq1 hquq hρ'0
  -- z ∈ ∂poly1
  have hzA : z ∈ poly1.toBoundarySet := hsub hzab
  -- z ∉ ∂poly1 ∩ ∂poly2 (since z ∉ ∂poly2)
  have hzF : z ∉ poly1.toBoundarySet ∩ poly2.toBoundarySet := fun h => hzoff h.2
  -- every point of [v,z] is within ρ' of q
  have hseg_close : ∀ x ∈ (LineSegment.mk v z).toSet, dist (vR x) (vR q) ≤ ρ' := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := vR_mem_seg hx
    rw [hxs]
    exact segR_dist_le (le_of_lt hvdist) (le_of_lt hzdist) s hs
  -- [v,z] cannot avoid Mlist
  have hnotavoid : ¬ (∀ x ∈ (LineSegment.mk v z).toSet, ∀ e0 ∈ Mlist poly1 poly2,
      x ∉ (LineSegment.mk e0.1 e0.2).toSet) := by
    intro havoid
    have hz1 : z ∈ poly1.interior :=
      (main_dir poly1 poly2 h1n h2n h1e h2e hfin havoid hzF hv1 hv2).1
    exact boundary_not_interior hzA hz1
  -- so [v,z] meets some Mlist edge near q
  rw [not_forall] at hnotavoid
  obtain ⟨x, hx⟩ := hnotavoid
  rw [not_forall] at hx
  obtain ⟨hxvz, hx⟩ := hx
  rw [not_forall] at hx
  obtain ⟨e0, he0x⟩ := hx
  rw [not_forall] at he0x
  obtain ⟨he0, hxe0⟩ := he0x
  rw [not_not] at hxe0
  -- x is within ρ' < ρ of q
  have hxclose : dist (vR x) (vR q) < ρ := lt_of_le_of_lt (hseg_close x hxvz) hρ'lt
  -- e0 must contain q
  have hqe0 : q ∈ (LineSegment.mk e0.1 e0.2).toSet := by
    by_contra hqe0
    obtain ⟨s, hs, hxs⟩ := vR_mem_seg hxe0
    have := hρ e0 he0 hqe0 s hs
    rw [← hxs, dist_comm] at this
    linarith [hxclose]
  -- q ∈ [p,q] is on the Mlist-edge e0 — contradiction with hpq
  have hqpq : q ∈ (LineSegment.mk p q).toSet := ⟨1, by norm_num, by norm_num, by ring, by ring⟩
  exact hpq q hqpq e0 he0 hqe0

/-- **A∩B-membership is constant along a segment avoiding every `Mlist`-edge.**  This is the key
geometric fact connecting the clipped boundary `Mlist` to `poly1.interior ∩ poly2.interior`. -/
theorem AcapB_const (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p q : Vector2D}
    (hpq : ∀ x ∈ (LineSegment.mk p q).toSet, ∀ e ∈ Mlist poly1 poly2,
        x ∉ (LineSegment.mk e.1 e.2).toSet) :
    (p ∈ poly1.interior ∩ poly2.interior ↔ q ∈ poly1.interior ∩ poly2.interior) := by
  -- `[q,p]` has the same point-set as `[p,q]`, so the avoidance is symmetric.
  have hqp : ∀ x ∈ (LineSegment.mk q p).toSet, ∀ e ∈ Mlist poly1 poly2,
      x ∉ (LineSegment.mk e.1 e.2).toSet := by
    intro x hx e he
    apply hpq x ?_ e he
    obtain ⟨t, ht0, ht1, hxx, hxy⟩ := hx
    exact ⟨1 - t, by linarith, by linarith, by rw [hxx]; ring, by rw [hxy]; ring⟩
  constructor
  · rintro ⟨hp1, hp2⟩
    have hqF := endpoint_off_double_C poly1 poly2 h1n h2n h1e h2e hfin hpq hp1 hp2
    exact main_dir poly1 poly2 h1n h2n h1e h2e hfin hpq hqF hp1 hp2
  · rintro ⟨hq1, hq2⟩
    have hpF := endpoint_off_double_C poly1 poly2 h1n h2n h1e h2e hfin hqp hq1 hq2
    exact main_dir poly1 poly2 h1n h2n h1e h2e hfin hqp hpF hq1 hq2

end Polygons2
end
