import Mathlib
import Polygons2.PolgonIntersection2Defs
import Polygons2.Geom
import Polygons2.RayIndep
import Polygons2.Interior
import Polygons2.SubRay
import Polygons2.RayParam
import Polygons2.ClipM

/-!
# Local constancy of the even–odd polygon interior across a boundary-free segment.

If the closed segment `[P,Q]` misses `poly`'s boundary entirely, then `P` and `Q` have the
same interior status.  The proof routes through a generic off-line point `R = R(k)` (midpoint
plus `k`·perpendicular) and flips interior status along the two boundary-free rays `[P,R]`,
`[R,Q]` using `flip_subRay`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-! ## Real embedding and segments over `ℝ` -/

/-- Cast a rational vector to `ℝ × ℝ`. -/
def vR (v : Vector2D) : ℝ × ℝ := (↑v.x, ↑v.y)

/-- A real segment point. -/
def segR (p q : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := ((1-t)*p.1 + t*q.1, (1-t)*p.2 + t*q.2)

lemma continuous_segR (p q : ℝ × ℝ) : Continuous (segR p q) := by
  unfold segR; fun_prop

/-! ## Separation of disjoint compact real segments -/

lemma seg_sep (p q a b : ℝ × ℝ)
    (hdisj : ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1, segR p q s ≠ segR a b u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1,
      δ ≤ dist (segR p q s) (segR a b u) := by
  set f : ℝ × ℝ → ℝ := fun w => dist (segR p q w.1) (segR a b w.2) with hf
  have hK : IsCompact ((Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1)) := (isCompact_Icc).prod (isCompact_Icc)
  have hne : ((Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1)).Nonempty := ⟨(0,0), by constructor <;> simp⟩
  have hcont : ContinuousOn f ((Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1)) := by
    apply Continuous.continuousOn
    exact ((continuous_segR p q).comp continuous_fst).dist ((continuous_segR a b).comp continuous_snd)
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne hcont
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨f w, dist_pos.mpr (hdisj w.1 hw1 w.2 hw2), ?_⟩
  intro s hs u hu
  exact hmin (show (s,u) ∈ _ from ⟨hs, hu⟩)

/-! ## Rational ⇒ real disjointness transfer -/

/-- Membership in a rational segment via the x-coordinate, for a point on the segment's line. -/
lemma mem_seg_of_x {p1 p2 w : Vector2D}
    (hline : (p2.x-p1.x)*(w.y-p1.y) - (p2.y-p1.y)*(w.x-p1.x) = 0)
    (hdx : p2.x - p1.x ≠ 0)
    (hbtw : (w.x - p1.x) / (p2.x - p1.x) ∈ Set.Icc (0:ℚ) 1) :
    w ∈ (LineSegment.mk p1 p2).toSet := by
  set t := (w.x - p1.x)/(p2.x-p1.x) with ht
  refine ⟨t, hbtw.1, hbtw.2, ?_, ?_⟩
  · rw [ht]; field_simp; ring
  · rw [ht]; field_simp; nlinarith [hline]

/-- Membership in a rational segment via the y-coordinate. -/
lemma mem_seg_of_y {p1 p2 w : Vector2D}
    (hline : (p2.x-p1.x)*(w.y-p1.y) - (p2.y-p1.y)*(w.x-p1.x) = 0)
    (hdy : p2.y - p1.y ≠ 0)
    (hbtw : (w.y - p1.y) / (p2.y - p1.y) ∈ Set.Icc (0:ℚ) 1) :
    w ∈ (LineSegment.mk p1 p2).toSet := by
  set t := (w.y - p1.y)/(p2.y-p1.y) with ht
  refine ⟨t, hbtw.1, hbtw.2, ?_, ?_⟩
  · rw [ht]; field_simp; nlinarith [hline]
  · rw [ht]; field_simp; ring

/-- Cramer: non-degenerate intersection has a rational common point. -/
lemma cramer_nondeg (P Q a b : Vector2D) (s u : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1)
    (heq : segR (vR P) (vR Q) s = segR (vR a) (vR b) u)
    (hdet : (Q.x-P.x)*(b.y-a.y) - (Q.y-P.y)*(b.x-a.x) ≠ 0) :
    ∃ p : Vector2D, p ∈ (LineSegment.mk P Q).toSet ∧ p ∈ (LineSegment.mk a b).toSet := by
  have h1 : (1-s)*(P.x:ℝ) + s*(Q.x:ℝ) = (1-u)*(a.x:ℝ) + u*(b.x:ℝ) := by
    have := congrArg Prod.fst heq; simpa [segR, vR] using this
  have h2 : (1-s)*(P.y:ℝ) + s*(Q.y:ℝ) = (1-u)*(a.y:ℝ) + u*(b.y:ℝ) := by
    have := congrArg Prod.snd heq; simpa [segR, vR] using this
  set DET : ℚ := (Q.x-P.x)*(b.y-a.y) - (Q.y-P.y)*(b.x-a.x) with hDET
  set sr : ℚ := ((a.x-P.x)*(b.y-a.y) - (a.y-P.y)*(b.x-a.x))/DET with hsr
  set ur : ℚ := ((Q.y-P.y)*(a.x-P.x) - (Q.x-P.x)*(a.y-P.y))/DET with hur
  have hDETr : ((DET:ℚ):ℝ) ≠ 0 := by exact_mod_cast hdet
  have hs_eq : s = (sr:ℝ) := by
    rw [hsr]; push_cast; rw [eq_div_iff hDETr, hDET]; push_cast
    linear_combination ((b.y:ℝ)-a.y) * h1 - ((b.x:ℝ)-a.x) * h2
  have hu_eq : u = (ur:ℝ) := by
    rw [hur]; push_cast; rw [eq_div_iff hDETr, hDET]; push_cast
    linear_combination ((Q.y:ℝ)-P.y) * h1 - ((Q.x:ℝ)-P.x) * h2
  have hsr0 : (0:ℚ) ≤ sr := by have : (0:ℝ) ≤ (sr:ℝ) := hs_eq ▸ hs.1; exact_mod_cast this
  have hsr1 : sr ≤ 1 := by have : (sr:ℝ) ≤ 1 := hs_eq ▸ hs.2; exact_mod_cast this
  have hur0 : (0:ℚ) ≤ ur := by have : (0:ℝ) ≤ (ur:ℝ) := hu_eq ▸ hu.1; exact_mod_cast this
  have hur1 : ur ≤ 1 := by have : (ur:ℝ) ≤ 1 := hu_eq ▸ hu.2; exact_mod_cast this
  refine ⟨⟨(1-sr)*P.x + sr*Q.x, (1-sr)*P.y + sr*Q.y⟩,
    ⟨sr, hsr0, hsr1, rfl, rfl⟩, ⟨ur, hur0, hur1, ?_, ?_⟩⟩
  · have : ((1-sr)*P.x + sr*Q.x : ℚ) = ((1-ur)*a.x+ur*b.x : ℚ) := by
      have hr : ((1-sr)*(P.x:ℝ) + sr*Q.x) = ((1-ur)*a.x+ur*b.x) := by
        rw [← hs_eq, ← hu_eq]; exact h1
      have := hr; push_cast at this; exact_mod_cast this
    simpa using this
  · have : ((1-sr)*P.y + sr*Q.y : ℚ) = ((1-ur)*a.y+ur*b.y : ℚ) := by
      have hr : ((1-sr)*(P.y:ℝ) + sr*Q.y) = ((1-ur)*a.y+ur*b.y) := by
        rw [← hs_eq, ← hu_eq]; exact h2
      have := hr; push_cast at this; exact_mod_cast this
    simpa using this

/-- In the degenerate case the endpoints `a,b` lie on the line through `P,Q`. -/
lemma ab_on_line (P Q a b : Vector2D) (s u : ℝ)
    (heq : segR (vR P) (vR Q) s = segR (vR a) (vR b) u)
    (hdet : (Q.x-P.x)*(b.y-a.y) - (Q.y-P.y)*(b.x-a.x) = 0) :
    (Q.x-P.x)*(a.y-P.y) - (Q.y-P.y)*(a.x-P.x) = 0 ∧
    (Q.x-P.x)*(b.y-P.y) - (Q.y-P.y)*(b.x-P.x) = 0 := by
  have h1 : (1-s)*(P.x:ℝ) + s*(Q.x:ℝ) = (1-u)*(a.x:ℝ) + u*(b.x:ℝ) := by
    have := congrArg Prod.fst heq; simpa [segR, vR] using this
  have h2 : (1-s)*(P.y:ℝ) + s*(Q.y:ℝ) = (1-u)*(a.y:ℝ) + u*(b.y:ℝ) := by
    have := congrArg Prod.snd heq; simpa [segR, vR] using this
  have hdetR : ((Q.x:ℝ)-P.x)*((b.y:ℝ)-a.y) - ((Q.y:ℝ)-P.y)*((b.x:ℝ)-a.x) = 0 := by
    have : (((Q.x-P.x)*(b.y-a.y) - (Q.y-P.y)*(b.x-a.x):ℚ):ℝ) = 0 := by rw [hdet]; simp
    push_cast at this; linarith [this]
  have key : ((Q.x:ℝ)-P.x)*((a.y:ℝ)-P.y) - ((Q.y:ℝ)-P.y)*((a.x:ℝ)-P.x) = 0 := by
    linear_combination (-(Q.x:ℝ)+P.x) * h2 + ((Q.y:ℝ)-P.y) * h1 - u * hdetR
  have keyb : ((Q.x:ℝ)-P.x)*((b.y:ℝ)-P.y) - ((Q.y:ℝ)-P.y)*((b.x:ℝ)-P.x) = 0 := by
    linear_combination (-(Q.x:ℝ)+P.x) * h2 + ((Q.y:ℝ)-P.y) * h1 + (1-u) * hdetR
  constructor
  · have : (((Q.x-P.x)*(a.y-P.y) - (Q.y-P.y)*(a.x-P.x):ℚ):ℝ) = 0 := by push_cast; linarith [key]
    exact_mod_cast this
  · have : (((Q.x-P.x)*(b.y-P.y) - (Q.y-P.y)*(b.x-P.x):ℚ):ℝ) = 0 := by push_cast; linarith [keyb]
    exact_mod_cast this

/-- 1-D overlap of two rational intervals witnessed by a real point. -/
lemma overlap1D (p q c d : ℚ) (r : ℝ)
    (h1 : min (p:ℝ) q ≤ r) (h2 : r ≤ max (p:ℝ) q)
    (h3 : min (c:ℝ) d ≤ r) (h4 : r ≤ max (c:ℝ) d) :
    ∃ L : ℚ, min p q ≤ L ∧ L ≤ max p q ∧ min c d ≤ L ∧ L ≤ max c d := by
  refine ⟨max (min p q) (min c d), le_max_left _ _, ?_, le_max_right _ _, ?_⟩
  · apply max_le (min_le_max)
    have hr : (min (c:ℝ) d) ≤ max (p:ℝ) q := le_trans h3 h2
    have : ((min c d : ℚ):ℝ) ≤ ((max p q : ℚ):ℝ) := by push_cast; exact hr
    exact_mod_cast this
  · apply max_le _ (min_le_max)
    have hr : (min (p:ℝ) q) ≤ max (c:ℝ) d := le_trans h1 h4
    have : ((min p q : ℚ):ℝ) ≤ ((max c d : ℚ):ℝ) := by push_cast; exact hr
    exact_mod_cast this

/-- `L` between `min p q` and `max p q` gives a parameter in `[0,1]`. -/
lemma param_mem {p q L : ℚ} (hd : q - p ≠ 0) (h1 : min p q ≤ L) (h2 : L ≤ max p q) :
    (L - p)/(q - p) ∈ Set.Icc (0:ℚ) 1 := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hqp : q < p := by linarith
    rw [min_eq_right (le_of_lt hqp)] at h1
    rw [max_eq_left (le_of_lt hqp)] at h2
    constructor
    · rw [div_nonneg_iff]; right; exact ⟨by linarith, by linarith⟩
    · rw [div_le_one_of_neg (by linarith)]; linarith
  · have hpq : p < q := by linarith
    rw [min_eq_left (le_of_lt hpq)] at h1
    rw [max_eq_right (le_of_lt hpq)] at h2
    constructor
    · rw [div_nonneg_iff]; left; exact ⟨by linarith, by linarith⟩
    · rw [div_le_one (by linarith)]; linarith

lemma collinear_trans {P Q a b W : Vector2D}
    (hDx : Q.x - P.x ≠ 0)
    (hla : (Q.x-P.x)*(a.y-P.y) - (Q.y-P.y)*(a.x-P.x) = 0)
    (hlb : (Q.x-P.x)*(b.y-P.y) - (Q.y-P.y)*(b.x-P.x) = 0)
    (hlW : (Q.x-P.x)*(W.y-P.y) - (Q.y-P.y)*(W.x-P.x) = 0) :
    (b.x-a.x)*(W.y-a.y) - (b.y-a.y)*(W.x-a.x) = 0 := by
  have key : (Q.x-P.x)*((b.x-a.x)*(W.y-a.y) - (b.y-a.y)*(W.x-a.x)) = 0 := by
    linear_combination (b.x-a.x)*hlW - (W.x-a.x)*hlb + (W.x-b.x)*hla
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hDx
  · exact h

lemma collinear_trans_y {P Q a b W : Vector2D}
    (hDy : Q.y - P.y ≠ 0)
    (hla : (Q.x-P.x)*(a.y-P.y) - (Q.y-P.y)*(a.x-P.x) = 0)
    (hlb : (Q.x-P.x)*(b.y-P.y) - (Q.y-P.y)*(b.x-P.x) = 0)
    (hlW : (Q.x-P.x)*(W.y-P.y) - (Q.y-P.y)*(W.x-P.x) = 0) :
    (b.x-a.x)*(W.y-a.y) - (b.y-a.y)*(W.x-a.x) = 0 := by
  have key : (Q.y-P.y)*((b.x-a.x)*(W.y-a.y) - (b.y-a.y)*(W.x-a.x)) = 0 := by
    linear_combination (W.y-b.y)*hla + (a.y-W.y)*hlb + (b.y-a.y)*hlW
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hDy
  · exact h

lemma deg_transfer_x (P Q a b : Vector2D) (hab : a ≠ b) (s u : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1)
    (heq : segR (vR P) (vR Q) s = segR (vR a) (vR b) u)
    (hdet : (Q.x-P.x)*(b.y-a.y) - (Q.y-P.y)*(b.x-a.x) = 0)
    (hDx : Q.x - P.x ≠ 0) :
    ∃ p : Vector2D, p ∈ (LineSegment.mk P Q).toSet ∧ p ∈ (LineSegment.mk a b).toSet := by
  obtain ⟨hla, hlb⟩ := ab_on_line P Q a b s u heq hdet
  have h1 : (1-s)*(P.x:ℝ) + s*(Q.x:ℝ) = (1-u)*(a.x:ℝ) + u*(b.x:ℝ) := by
    have := congrArg Prod.fst heq; simpa [segR, vR] using this
  have hax : b.x - a.x ≠ 0 := by
    intro h0
    apply hab
    have hbxax : b.x = a.x := by linarith [sub_eq_zero.mp h0]
    have hz : (Q.x-P.x)*(b.y-a.y) = 0 := by
      have hbb : (Q.x-P.x)*(b.y-P.y) - (Q.y-P.y)*(a.x-P.x) = 0 := by
        rw [← hbxax]; linarith [hlb]
      linear_combination hbb - hla
    have hby : b.y = a.y := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hDx
      · linarith [sub_eq_zero.mp h]
    ext <;> [exact hbxax.symm; exact hby.symm]
  set X : ℝ := (1-s)*(P.x:ℝ) + s*(Q.x:ℝ) with hX
  have hXpq : min (P.x:ℝ) Q.x ≤ X ∧ X ≤ max (P.x:ℝ) Q.x := by
    constructor
    · rw [hX]; rcases le_total (P.x:ℝ) Q.x with h | h
      · rw [min_eq_left h]; nlinarith [hs.1, hs.2]
      · rw [min_eq_right h]; nlinarith [hs.1, hs.2]
    · rw [hX]; rcases le_total (P.x:ℝ) Q.x with h | h
      · rw [max_eq_right h]; nlinarith [hs.1, hs.2]
      · rw [max_eq_left h]; nlinarith [hs.1, hs.2]
  have hXab : min (a.x:ℝ) b.x ≤ X ∧ X ≤ max (a.x:ℝ) b.x := by
    rw [h1]
    constructor
    · rcases le_total (a.x:ℝ) b.x with h | h
      · rw [min_eq_left h]; nlinarith [hu.1, hu.2]
      · rw [min_eq_right h]; nlinarith [hu.1, hu.2]
    · rcases le_total (a.x:ℝ) b.x with h | h
      · rw [max_eq_right h]; nlinarith [hu.1, hu.2]
      · rw [max_eq_left h]; nlinarith [hu.1, hu.2]
  obtain ⟨L, hLpq1, hLpq2, hLab1, hLab2⟩ :=
    overlap1D P.x Q.x a.x b.x X hXpq.1 hXpq.2 hXab.1 hXab.2
  set Wy : ℚ := P.y + (Q.y-P.y)*(L-P.x)/(Q.x-P.x) with hWy
  set W : Vector2D := ⟨L, Wy⟩ with hWdef
  have hWline : (Q.x-P.x)*(W.y-P.y) - (Q.y-P.y)*(W.x-P.x) = 0 := by
    simp only [hWdef, hWy]; field_simp; ring
  have hWxL : W.x = L := rfl
  have hParPQ : (W.x - P.x)/(Q.x-P.x) ∈ Set.Icc (0:ℚ) 1 := by
    rw [hWxL]; exact param_mem hDx hLpq1 hLpq2
  have hParAB : (W.x - a.x)/(b.x-a.x) ∈ Set.Icc (0:ℚ) 1 := by
    rw [hWxL]; exact param_mem hax hLab1 hLab2
  have hWmemPQ : W ∈ (LineSegment.mk P Q).toSet := mem_seg_of_x hWline hDx hParPQ
  have hWlineAB : (b.x-a.x)*(W.y-a.y) - (b.y-a.y)*(W.x-a.x) = 0 :=
    collinear_trans hDx hla hlb hWline
  have hWmemAB : W ∈ (LineSegment.mk a b).toSet := mem_seg_of_x hWlineAB hax hParAB
  exact ⟨W, hWmemPQ, hWmemAB⟩

lemma deg_transfer_y (P Q a b : Vector2D) (hab : a ≠ b) (s u : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1)
    (heq : segR (vR P) (vR Q) s = segR (vR a) (vR b) u)
    (hdet : (Q.x-P.x)*(b.y-a.y) - (Q.y-P.y)*(b.x-a.x) = 0)
    (hDy : Q.y - P.y ≠ 0) :
    ∃ p : Vector2D, p ∈ (LineSegment.mk P Q).toSet ∧ p ∈ (LineSegment.mk a b).toSet := by
  obtain ⟨hla, hlb⟩ := ab_on_line P Q a b s u heq hdet
  have h2 : (1-s)*(P.y:ℝ) + s*(Q.y:ℝ) = (1-u)*(a.y:ℝ) + u*(b.y:ℝ) := by
    have := congrArg Prod.snd heq; simpa [segR, vR] using this
  have hay : b.y - a.y ≠ 0 := by
    intro h0
    apply hab
    have hbyay : b.y = a.y := by linarith [sub_eq_zero.mp h0]
    have hz : (Q.y-P.y)*(b.x-a.x) = 0 := by
      have hbb : (Q.x-P.x)*(a.y-P.y) - (Q.y-P.y)*(b.x-P.x) = 0 := by
        rw [← hbyay]; linarith [hlb]
      linear_combination hla - hbb
    have hbx : b.x = a.x := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hDy
      · linarith [sub_eq_zero.mp h]
    ext <;> [exact hbx.symm; exact hbyay.symm]
  set X : ℝ := (1-s)*(P.y:ℝ) + s*(Q.y:ℝ) with hX
  have hXpq : min (P.y:ℝ) Q.y ≤ X ∧ X ≤ max (P.y:ℝ) Q.y := by
    constructor
    · rw [hX]; rcases le_total (P.y:ℝ) Q.y with h | h
      · rw [min_eq_left h]; nlinarith [hs.1, hs.2]
      · rw [min_eq_right h]; nlinarith [hs.1, hs.2]
    · rw [hX]; rcases le_total (P.y:ℝ) Q.y with h | h
      · rw [max_eq_right h]; nlinarith [hs.1, hs.2]
      · rw [max_eq_left h]; nlinarith [hs.1, hs.2]
  have hXab : min (a.y:ℝ) b.y ≤ X ∧ X ≤ max (a.y:ℝ) b.y := by
    rw [h2]
    constructor
    · rcases le_total (a.y:ℝ) b.y with h | h
      · rw [min_eq_left h]; nlinarith [hu.1, hu.2]
      · rw [min_eq_right h]; nlinarith [hu.1, hu.2]
    · rcases le_total (a.y:ℝ) b.y with h | h
      · rw [max_eq_right h]; nlinarith [hu.1, hu.2]
      · rw [max_eq_left h]; nlinarith [hu.1, hu.2]
  obtain ⟨L, hLpq1, hLpq2, hLab1, hLab2⟩ :=
    overlap1D P.y Q.y a.y b.y X hXpq.1 hXpq.2 hXab.1 hXab.2
  set Wx : ℚ := P.x + (Q.x-P.x)*(L-P.y)/(Q.y-P.y) with hWx
  set W : Vector2D := ⟨Wx, L⟩ with hWdef
  have hWline : (Q.x-P.x)*(W.y-P.y) - (Q.y-P.y)*(W.x-P.x) = 0 := by
    simp only [hWdef, hWx]; field_simp; ring
  have hWyL : W.y = L := rfl
  have hParPQ : (W.y - P.y)/(Q.y-P.y) ∈ Set.Icc (0:ℚ) 1 := by
    rw [hWyL]; exact param_mem hDy hLpq1 hLpq2
  have hParAB : (W.y - a.y)/(b.y-a.y) ∈ Set.Icc (0:ℚ) 1 := by
    rw [hWyL]; exact param_mem hay hLab1 hLab2
  have hWmemPQ : W ∈ (LineSegment.mk P Q).toSet := mem_seg_of_y hWline hDy hParPQ
  have hWlineAB : (b.x-a.x)*(W.y-a.y) - (b.y-a.y)*(W.x-a.x) = 0 :=
    collinear_trans_y hDy hla hlb hWline
  have hWmemAB : W ∈ (LineSegment.mk a b).toSet := mem_seg_of_y hWlineAB hay hParAB
  exact ⟨W, hWmemPQ, hWmemAB⟩

/-- Rational segments disjoint ⇒ their real casts are disjoint over `[0,1]`. -/
lemma real_disjoint (P Q a b : Vector2D) (hPQ : P ≠ Q) (hab : a ≠ b)
    (hdisj : ∀ p : Vector2D, p ∈ (LineSegment.mk P Q).toSet → p ∉ (LineSegment.mk a b).toSet) :
    ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1, segR (vR P) (vR Q) s ≠ segR (vR a) (vR b) u := by
  intro s hs u hu heq
  have hcontra : ∃ p : Vector2D,
      p ∈ (LineSegment.mk P Q).toSet ∧ p ∈ (LineSegment.mk a b).toSet := by
    by_cases hdet : (Q.x-P.x)*(b.y-a.y) - (Q.y-P.y)*(b.x-a.x) = 0
    · have hD : Q.x - P.x ≠ 0 ∨ Q.y - P.y ≠ 0 := by
        by_contra h; rw [not_or, not_not, not_not] at h
        apply hPQ
        have hx : P.x = Q.x := by linarith [sub_eq_zero.mp h.1]
        have hy : P.y = Q.y := by linarith [sub_eq_zero.mp h.2]
        ext <;> [exact hx; exact hy]
      rcases hD with hDx | hDy
      · exact deg_transfer_x P Q a b hab s u hs hu heq hdet hDx
      · exact deg_transfer_y P Q a b hab s u hs hu heq hdet hDy
    · exact cramer_nondeg P Q a b s u hs hu heq hdet
  obtain ⟨p, hpPQ, hpab⟩ := hcontra
  exact hdisj p hpPQ hpab

/-! ## Perturbation: the legs `[P,R]`, `[R,Q]` stay near `[P,Q]` -/

def midR (p q : ℝ × ℝ) : ℝ × ℝ := ((p.1+q.1)/2, (p.2+q.2)/2)
def perpR (p q : ℝ × ℝ) : ℝ × ℝ := (q.2 - p.2, -(q.1 - p.1))
def Rk (p q : ℝ × ℝ) (k : ℝ) : ℝ × ℝ :=
  ((midR p q).1 + k*(perpR p q).1, (midR p q).2 + k*(perpR p q).2)

lemma dist_shift (x : ℝ × ℝ) (a b : ℝ) : dist (x.1 + a, x.2 + b) x ≤ max |a| |b| := by
  rw [Prod.dist_eq]
  apply max_le_max <;> simp [Real.dist_eq]

lemma leg_avoids {p q a b c d : ℝ × ℝ} {δ ρ : ℝ}
    (hsep : ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1, δ ≤ dist (segR p q s) (segR a b u))
    (hρ : ρ < δ)
    (hclose : ∀ s ∈ Icc (0:ℝ) 1, ∃ s' ∈ Icc (0:ℝ) 1, dist (segR c d s) (segR p q s') ≤ ρ) :
    ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1, segR c d s ≠ segR a b u := by
  intro s hs u hu heq
  obtain ⟨s', hs', hclose'⟩ := hclose s hs
  have h1 : δ ≤ dist (segR p q s') (segR a b u) := hsep s' hs' u hu
  have htri : dist (segR p q s') (segR a b u) ≤ dist (segR p q s') (segR c d s) := by rw [heq]
  rw [dist_comm] at hclose'
  linarith [le_trans h1 htri, hclose']

lemma leg1_close (p q : ℝ × ℝ) (k : ℝ) (hk : 0 ≤ k) :
    ∀ s ∈ Icc (0:ℝ) 1, ∃ s' ∈ Icc (0:ℝ) 1,
      dist (segR p (Rk p q k) s) (segR p q s') ≤ k * max |(perpR p q).1| |(perpR p q).2| := by
  intro s hs
  refine ⟨s/2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
  have heq : segR p (Rk p q k) s
      = ((segR p q (s/2)).1 + s*k*(perpR p q).1, (segR p q (s/2)).2 + s*k*(perpR p q).2) := by
    unfold segR Rk midR perpR; ext <;> (simp; ring)
  rw [heq]
  refine le_trans (dist_shift (segR p q (s/2)) (s*k*(perpR p q).1) (s*k*(perpR p q).2)) ?_
  have hs0 := hs.1; have hs1 := hs.2
  have hsk : |s*k| ≤ k := by
    rw [abs_mul, abs_of_nonneg hs0, abs_of_nonneg hk]; nlinarith [hs1, hk]
  apply max_le
  · rw [show s*k*(perpR p q).1 = (s*k)*(perpR p q).1 from by ring, abs_mul]
    calc |s*k| * |(perpR p q).1| ≤ k * |(perpR p q).1| :=
            mul_le_mul_of_nonneg_right hsk (abs_nonneg _)
       _ ≤ k * max |(perpR p q).1| |(perpR p q).2| :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hk
  · rw [show s*k*(perpR p q).2 = (s*k)*(perpR p q).2 from by ring, abs_mul]
    calc |s*k| * |(perpR p q).2| ≤ k * |(perpR p q).2| :=
            mul_le_mul_of_nonneg_right hsk (abs_nonneg _)
       _ ≤ k * max |(perpR p q).1| |(perpR p q).2| :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) hk

lemma leg2_close (p q : ℝ × ℝ) (k : ℝ) (hk : 0 ≤ k) :
    ∀ s ∈ Icc (0:ℝ) 1, ∃ s' ∈ Icc (0:ℝ) 1,
      dist (segR (Rk p q k) q s) (segR p q s') ≤ k * max |(perpR p q).1| |(perpR p q).2| := by
  intro s hs
  refine ⟨(1+s)/2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
  have heq : segR (Rk p q k) q s
      = ((segR p q ((1+s)/2)).1 + (1-s)*k*(perpR p q).1,
         (segR p q ((1+s)/2)).2 + (1-s)*k*(perpR p q).2) := by
    unfold segR Rk midR perpR; ext <;> (simp; ring)
  rw [heq]
  refine le_trans (dist_shift (segR p q ((1+s)/2)) ((1-s)*k*(perpR p q).1)
    ((1-s)*k*(perpR p q).2)) ?_
  have hs0 := hs.1; have hs1 := hs.2
  have hsk : |(1-s)*k| ≤ k := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1-s), abs_of_nonneg hk]; nlinarith [hs0, hk]
  apply max_le
  · rw [show (1-s)*k*(perpR p q).1 = ((1-s)*k)*(perpR p q).1 from by ring, abs_mul]
    calc |(1-s)*k| * |(perpR p q).1| ≤ k * |(perpR p q).1| :=
            mul_le_mul_of_nonneg_right hsk (abs_nonneg _)
       _ ≤ k * max |(perpR p q).1| |(perpR p q).2| :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hk
  · rw [show (1-s)*k*(perpR p q).2 = ((1-s)*k)*(perpR p q).2 from by ring, abs_mul]
    calc |(1-s)*k| * |(perpR p q).2| ≤ k * |(perpR p q).2| :=
            mul_le_mul_of_nonneg_right hsk (abs_nonneg _)
       _ ≤ k * max |(perpR p q).1| |(perpR p q).2| :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) hk

/-! ## Rational `R(k)` and its real image -/

/-- The rational perturbed point: midpoint of `P,Q` plus `k`·(perpendicular). -/
def Rrat (P Q : Vector2D) (k : ℚ) : Vector2D :=
  ⟨(P.x+Q.x)/2 + k*(Q.y-P.y), (P.y+Q.y)/2 - k*(Q.x-P.x)⟩

lemma vR_Rrat (P Q : Vector2D) (k : ℚ) : vR (Rrat P Q k) = Rk (vR P) (vR Q) (k:ℝ) := by
  unfold vR Rrat Rk midR perpR
  ext
  · show ((((P.x+Q.x)/2 + k*(Q.y-P.y)):ℚ):ℝ) = _
    push_cast; ring
  · show ((((P.y+Q.y)/2 - k*(Q.x-P.x)):ℚ):ℝ) = _
    push_cast; ring

/-- A rational point on segment `[A,B]` corresponds to a real `segR` point with parameter in
`[0,1]`. -/
lemma vR_mem_seg {A B p : Vector2D} (hp : p ∈ (LineSegment.mk A B).toSet) :
    ∃ t : ℝ, t ∈ Icc (0:ℝ) 1 ∧ vR p = segR (vR A) (vR B) t := by
  obtain ⟨t, ht0, ht1, hx, hy⟩ := hp
  refine ⟨(t:ℝ), ⟨by exact_mod_cast ht0, by exact_mod_cast ht1⟩, ?_⟩
  unfold vR segR; ext
  · push_cast [hx]; ring
  · push_cast [hy]; ring

/-! ## Per-edge boundary-free bound for small `k` -/

/-- `Mrat P Q` bounds the perpendicular's coordinates: it casts to the sup-norm of `perpR`. -/
def Mrat (P Q : Vector2D) : ℚ := max |Q.y - P.y| |Q.x - P.x|

lemma perp_norm_eq (P Q : Vector2D) :
    max |(perpR (vR P) (vR Q)).1| |(perpR (vR P) (vR Q)).2| = ((Mrat P Q : ℚ):ℝ) := by
  have e1 : |(perpR (vR P) (vR Q)).1| = ((|Q.y - P.y| : ℚ):ℝ) := by
    unfold perpR vR; simp only
    rw [show ((Q.y:ℝ) - (P.y:ℝ)) = (((Q.y - P.y : ℚ)):ℝ) from by push_cast; ring,
        ← Rat.cast_abs]
  have e2 : |(perpR (vR P) (vR Q)).2| = ((|Q.x - P.x| : ℚ):ℝ) := by
    unfold perpR vR; simp only
    rw [show (-((Q.x:ℝ) - (P.x:ℝ))) = ((-(Q.x - P.x) : ℚ):ℝ) from by push_cast; ring,
        ← Rat.cast_abs, abs_neg]
  rw [e1, e2, Mrat]
  push_cast; rfl

lemma Mrat_nonneg (P Q : Vector2D) : 0 ≤ Mrat P Q := le_trans (abs_nonneg _) (le_max_left _ _)

/-- Generic per-edge boundary-free bound: if the leg (given by a closeness function with the
real `Rk`) stays within `↑(k·Mrat)` of `[P,Q]`, and `[P,Q]` misses edge `[a,b]`, then for small
`k` the leg's rational points miss `[a,b]`. -/
lemma leg_bf_of_close (P Q a b : Vector2D) (hPQ : P ≠ Q) (hab : a ≠ b)
    (hdisj : ∀ p : Vector2D, p ∈ (LineSegment.mk P Q).toSet → p ∉ (LineSegment.mk a b).toSet)
    (legR : ℝ → ℝ → ℝ × ℝ)
    (hclose : ∀ k : ℝ, 0 ≤ k → ∀ s ∈ Icc (0:ℝ) 1, ∃ s' ∈ Icc (0:ℝ) 1,
        dist (legR k s) (segR (vR P) (vR Q) s') ≤ k * ((Mrat P Q : ℚ):ℝ))
    (legQ : ℚ → LineSegment)
    (hlegQ : ∀ k : ℚ, ∀ p : Vector2D, p ∈ (legQ k).toSet →
        ∃ s ∈ Icc (0:ℝ) 1, vR p = legR (k:ℝ) s) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ p : Vector2D, p ∈ (legQ k).toSet → p ∉ (LineSegment.mk a b).toSet := by
  obtain ⟨δ, hδ, hsep⟩ := seg_sep (vR P) (vR Q) (vR a) (vR b)
    (real_disjoint P Q a b hPQ hab hdisj)
  -- choose rational c with 0 < c < δ
  obtain ⟨c, hc0, hcδ⟩ := exists_rat_btwn hδ
  have hc0' : 0 < c := by exact_mod_cast hc0
  set ε : ℚ := c / (Mrat P Q + 1) with hε
  have hMpos : (0:ℚ) < Mrat P Q + 1 := by have := Mrat_nonneg P Q; linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  refine ⟨ε, hε0, ?_⟩
  intro k hk0 hkε p hp hpab
  obtain ⟨s, hs, hps⟩ := hlegQ k p hp
  obtain ⟨t, ht0, ht1, hpA⟩ := hpab
  -- the real leg point equals the real edge point
  have hkR : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast le_of_lt hk0
  obtain ⟨s', hs', hcl⟩ := hclose (k:ℝ) hkR s hs
  -- p as a point of edge [a,b] in real coords
  have hpe : vR p = segR (vR a) (vR b) (t:ℝ) := by
    unfold vR segR; ext
    · push_cast [hpA.1]; ring
    · push_cast [hpA.2]; ring
  have hte : (t:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by exact_mod_cast ht0, by exact_mod_cast ht1⟩
  -- ρ = k*Mrat < δ
  have hρlt : (k:ℝ) * ((Mrat P Q : ℚ):ℝ) < δ := by
    have hkMle : k * Mrat P Q ≤ ε * Mrat P Q :=
      mul_le_mul_of_nonneg_right hkε (Mrat_nonneg P Q)
    have hεM : ε * Mrat P Q ≤ c := by
      rw [hε, div_mul_eq_mul_div, div_le_iff₀ hMpos]
      have := Mrat_nonneg P Q; nlinarith [this, hc0']
    have : (k:ℝ) * ((Mrat P Q:ℚ):ℝ) ≤ ((c:ℚ):ℝ) := by
      have h := le_trans hkMle hεM
      calc (k:ℝ) * ((Mrat P Q:ℚ):ℝ) = (((k * Mrat P Q : ℚ)):ℝ) := by push_cast; ring
        _ ≤ ((c:ℚ):ℝ) := by exact_mod_cast h
    linarith [this, hcδ]
  -- now apply leg_avoids-style contradiction
  have hsepP : δ ≤ dist (segR (vR P) (vR Q) s') (segR (vR a) (vR b) (t:ℝ)) := hsep s' hs' t hte
  have hcl' : dist (segR (vR P) (vR Q) s') (legR (k:ℝ) s) ≤ (k:ℝ) * ((Mrat P Q:ℚ):ℝ) := by
    rw [dist_comm]; exact hcl
  have heqpt : legR (k:ℝ) s = segR (vR a) (vR b) (t:ℝ) := by rw [← hps, hpe]
  have htri : dist (segR (vR P) (vR Q) s') (segR (vR a) (vR b) (t:ℝ))
      ≤ dist (segR (vR P) (vR Q) s') (legR (k:ℝ) s) := by rw [heqpt]
  linarith [le_trans hsepP htri, hcl', hρlt]

/-! ## Boundary-free for both legs, uniformly over all edges -/

/-- For a finite list of edges, each giving a small-`k` boundary-free bound, there is a single
positive `ε` working for all of them. -/
lemma exists_uniform_eps {α : Type*} (l : List α) (good : α → ℚ → Prop)
    (hmono : ∀ a, ∀ ε ε' : ℚ, 0 < ε' → ε' ≤ ε → good a ε → good a ε')
    (h : ∀ a ∈ l, ∃ ε : ℚ, 0 < ε ∧ good a ε) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ a ∈ l, good a ε := by
  induction l with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons x t ih =>
    obtain ⟨εx, hεx, hgx⟩ := h x (by simp)
    obtain ⟨εt, hεt, hgt⟩ := ih (fun a ha => h a (by simp [ha]))
    refine ⟨min εx εt, lt_min hεx hεt, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hmono a εx (min εx εt) (lt_min hεx hεt) (min_le_left _ _) hgx
    · exact hmono a εt (min εx εt) (lt_min hεx hεt) (min_le_right _ _) (hgt a ha')

/-- Boundary-free bound for leg `[P, R(k)]`: for small `k` the leg misses every edge of `poly`. -/
lemma leg1_bf (P Q : Vector2D) (hPQ : P ≠ Q) (poly : Polygon)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hdisj : ∀ e ∈ poly.segments, ∀ p : Vector2D,
        p ∈ (LineSegment.mk P Q).toSet → p ∉ e.toSet) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ p : Vector2D, p ∈ (LineSegment.mk P (Rrat P Q k)).toSet → p ∉ poly.toBoundarySet := by
  -- per-edge bound
  have hedge : ∀ e ∈ poly.segments, ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ p : Vector2D, p ∈ (LineSegment.mk P (Rrat P Q k)).toSet → p ∉ e.toSet := by
    intro e he
    obtain ⟨a, b⟩ := e
    exact leg_bf_of_close P Q a b hPQ (hnd ⟨a,b⟩ he) (hdisj ⟨a,b⟩ he)
      (fun k s => segR (vR P) (Rk (vR P) (vR Q) k) s)
      (fun k hk s hs => by
        obtain ⟨s', hs', hd⟩ := leg1_close (vR P) (vR Q) k hk s hs
        rw [perp_norm_eq] at hd; exact ⟨s', hs', hd⟩)
      (fun k => LineSegment.mk P (Rrat P Q k))
      (fun k p hp => by
        obtain ⟨t, ht, hpt⟩ := vR_mem_seg hp
        exact ⟨t, ht, by rw [hpt, vR_Rrat]⟩)
  obtain ⟨ε, hε, hgood⟩ := exists_uniform_eps poly.segments
    (fun e ε => ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ p : Vector2D, p ∈ (LineSegment.mk P (Rrat P Q k)).toSet → p ∉ e.toSet)
    (fun e ε ε' hε' hle hg k hk0 hkε p hp => hg k hk0 (le_trans hkε hle) p hp)
    hedge
  refine ⟨ε, hε, ?_⟩
  intro k hk0 hkε p hp hpb
  obtain ⟨e, he, hpe⟩ := hpb
  exact hgood e he k hk0 hkε p hp hpe

/-- Boundary-free bound for leg `[R(k), Q]`. -/
lemma leg2_bf (P Q : Vector2D) (hPQ : P ≠ Q) (poly : Polygon)
    (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hdisj : ∀ e ∈ poly.segments, ∀ p : Vector2D,
        p ∈ (LineSegment.mk P Q).toSet → p ∉ e.toSet) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ p : Vector2D, p ∈ (LineSegment.mk (Rrat P Q k) Q).toSet → p ∉ poly.toBoundarySet := by
  have hedge : ∀ e ∈ poly.segments, ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ p : Vector2D, p ∈ (LineSegment.mk (Rrat P Q k) Q).toSet → p ∉ e.toSet := by
    intro e he
    obtain ⟨a, b⟩ := e
    exact leg_bf_of_close P Q a b hPQ (hnd ⟨a,b⟩ he) (hdisj ⟨a,b⟩ he)
      (fun k s => segR (Rk (vR P) (vR Q) k) (vR Q) s)
      (fun k hk s hs => by
        obtain ⟨s', hs', hd⟩ := leg2_close (vR P) (vR Q) k hk s hs
        rw [perp_norm_eq] at hd; exact ⟨s', hs', hd⟩)
      (fun k => LineSegment.mk (Rrat P Q k) Q)
      (fun k p hp => by
        obtain ⟨t, ht, hpt⟩ := vR_mem_seg hp
        exact ⟨t, ht, by rw [hpt, vR_Rrat]⟩)
  obtain ⟨ε, hε, hgood⟩ := exists_uniform_eps poly.segments
    (fun e ε => ∀ k : ℚ, 0 < k → k ≤ ε →
      ∀ p : Vector2D, p ∈ (LineSegment.mk (Rrat P Q k) Q).toSet → p ∉ e.toSet)
    (fun e ε ε' hε' hle hg k hk0 hkε p hp => hg k hk0 (le_trans hkε hle) p hp)
    hedge
  refine ⟨ε, hε, ?_⟩
  intro k hk0 hkε p hp hpb
  obtain ⟨e, he, hpe⟩ := hpb
  exact hgood e he k hk0 hkε p hp hpe

/-! ## Vertices lie on the boundary (for polygons with ≥ 1 edge) -/

lemma vertex_mem_boundary {poly : Polygon} {w : Vector2D} (hw : w ∈ poly.vertices) :
    w ∈ poly.toBoundarySet ∨ poly.segments = [] := by
  rcases hv : poly.vertices with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · right; exact segs_nil hv
  · right; exact segs_single hv
  · left
    have hlist : w ∈ (v0 :: v1 :: rest) := by rw [← hv]; exact hw
    set L := v0 :: v1 :: rest with hL
    set L2 := (v1 :: rest) ++ [v0] with hL2
    have hlen : L.length = L2.length := by simp [hL, hL2]
    rw [List.mem_iff_getElem] at hlist
    obtain ⟨i, hi, hwi⟩ := hlist
    refine ⟨⟨w, L2[i]'(by rw [← hlen]; exact hi)⟩, ?_, ?_⟩
    · rw [segs_cons2 hv, List.mem_map]
      refine ⟨(L[i]'hi, L2[i]'(by rw [← hlen]; exact hi)), ?_, ?_⟩
      · rw [List.mem_iff_getElem]
        refine ⟨i, ?_, ?_⟩
        · rw [List.length_zip, ← hlen, Nat.min_self]; exact hi
        · rw [List.getElem_zip]
      · simp [hwi]
    · exact ⟨0, le_refl _, by norm_num, by simp [hwi], by simp [hwi]⟩

/-! ## Vertex-avoidance: a finite bad-`k` set -/

lemma cross1_eq (P Q w : Vector2D) (k : ℚ) :
    cross (vsub (Rrat P Q k) P) (vsub w P)
      = (cross (vsub Q P) (vsub w P))/2
        + k * ((Q.y-P.y)*(w.y-P.y) + (Q.x-P.x)*(w.x-P.x)) := by
  unfold Rrat vsub cross; simp; ring

lemma cross2_eq (P Q w : Vector2D) (k : ℚ) :
    cross (vsub Q (Rrat P Q k)) (vsub w (Rrat P Q k))
      = (cross (vsub Q P) (vsub w Q))/2
        + k * (-((Q.y-P.y)*(w.y-Q.y) + (Q.x-P.x)*(w.x-Q.x))) := by
  unfold Rrat vsub cross; simp; ring

lemma eq_zero_of_cross_dot {D v : Vector2D} (hD : D ≠ ⟨0,0⟩)
    (hc : cross D v = 0) (hd : dot D v = 0) : v = ⟨0,0⟩ := by
  have hpos : 0 < dot D D := dot_pos_of_ne_zero hD
  simp only [cross_def, dot_def] at hc hd
  have hx : v.x * (D.x^2 + D.y^2) = 0 := by linear_combination D.x * hd - D.y * hc
  have hy : v.y * (D.x^2 + D.y^2) = 0 := by linear_combination D.y * hd + D.x * hc
  have hsum : D.x^2 + D.y^2 ≠ 0 := by simp only [dot_def] at hpos; nlinarith [hpos]
  ext
  · rcases mul_eq_zero.mp hx with h | h
    · exact h
    · exact absurd h hsum
  · rcases mul_eq_zero.mp hy with h | h
    · exact h
    · exact absurd h hsum

lemma exists_bad_k (P Q : Vector2D) (hPQ : P ≠ Q) (verts : List Vector2D)
    (hP : ∀ w ∈ verts, w ≠ P) (hQ : ∀ w ∈ verts, w ≠ Q) :
    ∃ B : Finset ℚ, ∀ k : ℚ, k ∉ B → ∀ w ∈ verts,
      cross (vsub (Rrat P Q k) P) (vsub w P) ≠ 0 ∧
      cross (vsub Q (Rrat P Q k)) (vsub w (Rrat P Q k)) ≠ 0 := by
  set root1 : Vector2D → Option ℚ := fun w =>
    if dot (vsub Q P) (vsub w P) ≠ 0 then
      some (-(cross (vsub Q P) (vsub w P)/2) / (dot (vsub Q P) (vsub w P))) else none with hr1
  set root2 : Vector2D → Option ℚ := fun w =>
    if dot (vsub Q P) (vsub w Q) ≠ 0 then
      some ((cross (vsub Q P) (vsub w Q)/2) / (dot (vsub Q P) (vsub w Q))) else none with hr2
  set B : Finset ℚ := (verts.filterMap root1).toFinset ∪ (verts.filterMap root2).toFinset with hB
  refine ⟨B, ?_⟩
  intro k hk w hw
  have hwP : w ≠ P := hP w hw
  have hwQ : w ≠ Q := hQ w hw
  have hD : (vsub Q P) ≠ ⟨0,0⟩ := by
    intro hh; apply hPQ; ext
    · have := congrArg Vector2D.x hh; simp [vsub] at this; linarith
    · have := congrArg Vector2D.y hh; simp [vsub] at this; linarith
  constructor
  · rw [cross1_eq]
    have hm1eq : (Q.y-P.y)*(w.y-P.y) + (Q.x-P.x)*(w.x-P.x) = dot (vsub Q P) (vsub w P) := by
      simp [dot, vsub]; ring
    rw [hm1eq]
    by_cases hm1 : dot (vsub Q P) (vsub w P) = 0
    · rw [hm1, mul_zero, add_zero]
      intro hc
      have hcross : cross (vsub Q P) (vsub w P) = 0 := by linarith [hc]
      have hz : (vsub w P) = ⟨0,0⟩ := eq_zero_of_cross_dot hD hcross hm1
      apply hwP; ext
      · have := congrArg Vector2D.x hz; simp [vsub] at this; linarith
      · have := congrArg Vector2D.y hz; simp [vsub] at this; linarith
    · intro hc
      have hkroot : k = -(cross (vsub Q P) (vsub w P)/2) / (dot (vsub Q P) (vsub w P)) := by
        field_simp at hc ⊢; linarith [hc]
      apply hk
      rw [hB, Finset.mem_union]; left
      rw [List.mem_toFinset, List.mem_filterMap]
      exact ⟨w, hw, by simp only [hr1, if_pos hm1]; rw [hkroot]⟩
  · rw [cross2_eq]
    have hm2eq : -((Q.y-P.y)*(w.y-Q.y) + (Q.x-P.x)*(w.x-Q.x)) = -dot (vsub Q P) (vsub w Q) := by
      simp [dot, vsub]; ring
    rw [hm2eq]
    by_cases hm2 : dot (vsub Q P) (vsub w Q) = 0
    · rw [hm2, neg_zero, mul_zero, add_zero]
      intro hc
      have hcross : cross (vsub Q P) (vsub w Q) = 0 := by linarith [hc]
      have hz : (vsub w Q) = ⟨0,0⟩ := eq_zero_of_cross_dot hD hcross hm2
      apply hwQ; ext
      · have := congrArg Vector2D.x hz; simp [vsub] at this; linarith
      · have := congrArg Vector2D.y hz; simp [vsub] at this; linarith
    · intro hc
      have hkroot : k = (cross (vsub Q P) (vsub w Q)/2) / (dot (vsub Q P) (vsub w Q)) := by
        field_simp at hc ⊢; linarith [hc]
      apply hk
      rw [hB, Finset.mem_union]; right
      rw [List.mem_toFinset, List.mem_filterMap]
      exact ⟨w, hw, by simp only [hr2, if_pos hm2]; rw [hkroot]⟩

lemma dir1_nonzero (P Q : Vector2D) (hPQ : P ≠ Q) (k : ℚ) :
    vsub (Rrat P Q k) P ≠ ⟨0,0⟩ := by
  intro h
  have hD : (vsub Q P) ≠ ⟨0,0⟩ := by
    intro hh; apply hPQ; ext
    · have := congrArg Vector2D.x hh; simp [vsub] at this; linarith
    · have := congrArg Vector2D.y hh; simp [vsub] at this; linarith
  have hx := congrArg Vector2D.x h
  have hy := congrArg Vector2D.y h
  simp only [vsub, Rrat] at hx hy
  have hsum : ((Q.x-P.x)^2 + (Q.y-P.y)^2) * (1/4 + k^2) = 0 := by nlinarith [hx, hy]
  have hDsq : 0 < (Q.x-P.x)^2 + (Q.y-P.y)^2 := by
    rcases eq_or_ne (Q.x-P.x) 0 with h1 | h1
    · rcases eq_or_ne (Q.y-P.y) 0 with h2 | h2
      · exact absurd (by ext <;> simp [vsub] <;> linarith [h1,h2] : (vsub Q P) = ⟨0,0⟩) hD
      · positivity
    · positivity
  nlinarith [hsum, hDsq, sq_nonneg k]

lemma dir2_nonzero (P Q : Vector2D) (hPQ : P ≠ Q) (k : ℚ) :
    vsub Q (Rrat P Q k) ≠ ⟨0,0⟩ := by
  intro h
  have hD : (vsub Q P) ≠ ⟨0,0⟩ := by
    intro hh; apply hPQ; ext
    · have := congrArg Vector2D.x hh; simp [vsub] at this; linarith
    · have := congrArg Vector2D.y hh; simp [vsub] at this; linarith
  have hx := congrArg Vector2D.x h
  have hy := congrArg Vector2D.y h
  simp only [vsub, Rrat] at hx hy
  have hsum : ((Q.x-P.x)^2 + (Q.y-P.y)^2) * (1/4 + k^2) = 0 := by nlinarith [hx, hy]
  have hDsq : 0 < (Q.x-P.x)^2 + (Q.y-P.y)^2 := by
    rcases eq_or_ne (Q.x-P.x) 0 with h1 | h1
    · rcases eq_or_ne (Q.y-P.y) 0 with h2 | h2
      · exact absurd (by ext <;> simp [vsub] <;> linarith [h1,h2] : (vsub Q P) = ⟨0,0⟩) hD
      · positivity
    · positivity
  nlinarith [hsum, hDsq, sq_nonneg k]

/-! ## The hop lemma -/

/-- A point of the ray `⟨A, B−A⟩` at parameter `≤ 1` lies on the segment `[A,B]`. -/
lemma ray_le_one_mem_seg (A B : Vector2D) (hAB : vsub B A ≠ ⟨0,0⟩)
    {x : Vector2D} (hx : x ∈ (Ray.mk A (vsub B A) hAB).toSet)
    (hle : rayParam (Ray.mk A (vsub B A) hAB) x ≤ 1) :
    x ∈ (LineSegment.mk A B).toSet := by
  obtain ⟨hxx, hxy, hx0⟩ := rayParam_spec (Ray.mk A (vsub B A) hAB) hx
  refine ⟨rayParam (Ray.mk A (vsub B A) hAB) x, hx0, hle, ?_, ?_⟩
  · simp only [vsub] at hxx ⊢; rw [hxx]; ring
  · simp only [vsub] at hxy ⊢; rw [hxy]; ring

/-- `B` is at ray-parameter `1` along `⟨A, B−A⟩`; its origin point at param `1` is `B`. -/
lemma subRay_one_origin (A B : Vector2D) (hAB : vsub B A ≠ ⟨0,0⟩) :
    (subRay (Ray.mk A (vsub B A) hAB) 1).origin = B := by
  simp only [subRay_origin]; ext <;> simp [vsub]

lemma subRay_zero_origin (A B : Vector2D) (hAB : vsub B A ≠ ⟨0,0⟩) :
    (subRay (Ray.mk A (vsub B A) hAB) 0).origin = A := by
  simp only [subRay_origin]; ext <;> simp

/-- The hop: if the ray `⟨A, B−A⟩` avoids `poly`'s vertices and `[A,B]` misses the boundary,
then `A` and `B` have the same interior status. -/
lemma hop (poly : Polygon) (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (A B : Vector2D) (hAB : vsub B A ≠ ⟨0,0⟩)
    (hav : rayAvoidsVertices (Ray.mk A (vsub B A) hAB) poly)
    (hbf : ∀ x ∈ (LineSegment.mk A B).toSet, x ∉ poly.toBoundarySet) :
    A ∈ poly.interior ↔ B ∈ poly.interior := by
  have hbf' : ∀ x ∈ (Ray.mk A (vsub B A) hAB).toSet,
      rayParam (Ray.mk A (vsub B A) hAB) x ≤ 1 → x ∉ poly.toBoundarySet := by
    intro x hx hle
    exact hbf x (ray_le_one_mem_seg A B hAB hx hle)
  have h := flip_subRay (rr := Ray.mk A (vsub B A) hAB) (t₁ := 0) (t₂ := 1)
    (le_refl 0) (by norm_num) hnd hav hbf'
  rw [subRay_zero_origin A B hAB, subRay_one_origin A B hAB] at h
  exact h

/-- A ray `⟨O, d⟩` avoids `poly`'s vertices provided `cross d (w − O) ≠ 0` for every vertex. -/
lemma rayAvoidsVertices_of_cross (O d : Vector2D) (hd : d ≠ ⟨0,0⟩) (poly : Polygon)
    (h : ∀ w ∈ poly.vertices, cross d (vsub w O) ≠ 0) :
    rayAvoidsVertices (Ray.mk O d hd) poly := by
  rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hwr, hwv⟩
  have hcr : cross (Ray.mk O d hd).direction (vsub w (Ray.mk O d hd).origin) = 0 :=
    ((mem_ray_iff (Ray.mk O d hd) w).1 hwr).1
  simp only at hcr
  exact h w hwv hcr

/-! ## Main theorem -/

/-- The core 2-hop argument: works for ANY polygon, provided neither `P` nor `Q` is a vertex.
The boundary-free segment `[P,Q]` lets us perturb to a generic off-line point `R = R(k)` and
flip interior status along the two boundary-free, vertex-avoiding rays `[P,R]`, `[R,Q]`. -/
theorem constancy_of_notVertex {poly : Polygon} (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    {P Q : Vector2D} (hPQ : P ≠ Q)
    (hvP : ∀ w ∈ poly.vertices, w ≠ P) (hvQ : ∀ w ∈ poly.vertices, w ≠ Q)
    (hbf : ∀ x ∈ (LineSegment.mk P Q).toSet, x ∉ poly.toBoundarySet) :
    P ∈ poly.interior ↔ Q ∈ poly.interior := by
  have hdisj : ∀ e ∈ poly.segments, ∀ p : Vector2D,
      p ∈ (LineSegment.mk P Q).toSet → p ∉ e.toSet := by
    intro e he p hp hpe; exact hbf p hp ⟨e, he, hpe⟩
  obtain ⟨ε1, hε1, hbf1⟩ := leg1_bf P Q hPQ poly hnd hdisj
  obtain ⟨ε2, hε2, hbf2⟩ := leg2_bf P Q hPQ poly hnd hdisj
  obtain ⟨B, hBav⟩ := exists_bad_k P Q hPQ poly.vertices hvP hvQ
  have hposm : 0 < min ε1 ε2 := lt_min hε1 hε2
  obtain ⟨k, hk⟩ : ∃ k : ℚ, k ∈ (Set.Ioo (0:ℚ) (min ε1 ε2)) \ (B : Set ℚ) :=
    ((Set.Ioo_infinite hposm).diff B.finite_toSet).nonempty
  obtain ⟨⟨hk0, hkε⟩, hkB⟩ := hk
  have hkB' : k ∉ B := by simpa using hkB
  have hkε1 : k ≤ ε1 := le_of_lt (lt_of_lt_of_le hkε (min_le_left _ _))
  have hkε2 : k ≤ ε2 := le_of_lt (lt_of_lt_of_le hkε (min_le_right _ _))
  set R := Rrat P Q k with hR
  have hav := hBav k hkB'
  have hd1 : vsub R P ≠ ⟨0,0⟩ := dir1_nonzero P Q hPQ k
  have hav1 : rayAvoidsVertices (Ray.mk P (vsub R P) hd1) poly :=
    rayAvoidsVertices_of_cross P (vsub R P) hd1 poly (fun w hw => (hav w hw).1)
  have hd2 : vsub Q R ≠ ⟨0,0⟩ := dir2_nonzero P Q hPQ k
  have hav2 : rayAvoidsVertices (Ray.mk R (vsub Q R) hd2) poly :=
    rayAvoidsVertices_of_cross R (vsub Q R) hd2 poly (fun w hw => (hav w hw).2)
  have hbfPR : ∀ x ∈ (LineSegment.mk P R).toSet, x ∉ poly.toBoundarySet := hbf1 k hk0 hkε1
  have hbfRQ : ∀ x ∈ (LineSegment.mk R Q).toSet, x ∉ poly.toBoundarySet := hbf2 k hk0 hkε2
  have hop1 : P ∈ poly.interior ↔ R ∈ poly.interior := hop poly hnd P R hd1 hav1 hbfPR
  have hop2 : R ∈ poly.interior ↔ Q ∈ poly.interior := hop poly hnd R Q hd2 hav2 hbfRQ
  exact hop1.trans hop2

/-- A point that is a vertex of an edgeless polygon is in its interior (vacuously: every ray
from it meets that vertex, so no vertex-avoiding ray exists). -/
lemma vertex_mem_interior_of_no_segments {poly : Polygon} (hseg : poly.segments = [])
    {p : Vector2D} (hp : p ∈ poly.vertices) : p ∈ poly.interior := by
  refine ⟨?_, ?_⟩
  · intro seg hseg'; rw [hseg] at hseg'; exact absurd hseg' (by simp)
  · intro r hro hav
    exfalso
    rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem] at hav
    exact hav p ⟨by rw [← hro]; exact ⟨0, le_refl _, by simp, by simp⟩, hp⟩

/-- A point that is not a vertex of an edgeless polygon is not in its interior (a generic ray
from it avoids the finitely many vertices and crosses no edge). -/
lemma notVertex_notMem_interior_of_no_segments {poly : Polygon} (hseg : poly.segments = [])
    {p : Vector2D} (hp : p ∉ poly.vertices) : p ∉ poly.interior := by
  intro hint
  obtain ⟨_, hcnt⟩ := hint
  -- build a vertex-avoiding ray from p
  have hpV : ∀ w ∈ poly.vertices, w ≠ p := fun w hw hwp => hp (hwp ▸ hw)
  obtain ⟨c, _, _, hkav⟩ := exists_good_dir p ⟨1,0⟩ ⟨1,0⟩ poly.vertices
    (by intro h; simp [Vector2D.ext_iff] at h) (by intro h; simp [Vector2D.ext_iff] at h) hpV
  have hd3 : (⟨1, c⟩ : Vector2D) ≠ ⟨0, 0⟩ := by intro h; simp [Vector2D.ext_iff] at h
  have hav : rayAvoidsVertices (⟨p, ⟨1, c⟩, hd3⟩ : Ray) poly := by
    rw [rayAvoidsVertices, Set.eq_empty_iff_forall_notMem]
    rintro w ⟨⟨t, ht0, htx, hty⟩, hwv⟩
    exact hkav w hwv ⟨t, ht0, htx, hty⟩
  have := hcnt (⟨p, ⟨1, c⟩, hd3⟩ : Ray) rfl hav
  rw [intersectionRayPolygonSegmentsNumber, hseg] at this
  simp at this

theorem even_odd_constancy {poly : Polygon} (hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2)
    (hne : poly.segments ≠ [])
    {P Q : Vector2D}
    (hbf : ∀ x ∈ (LineSegment.mk P Q).toSet, x ∉ poly.toBoundarySet) :
    P ∈ poly.interior ↔ Q ∈ poly.interior := by
  rcases eq_or_ne P Q with hPQ | hPQ
  · rw [hPQ]
  have hPbf : P ∉ poly.toBoundarySet := hbf P ⟨0, by norm_num, by norm_num, by ring, by ring⟩
  have hQbf : Q ∉ poly.toBoundarySet := hbf Q ⟨1, by norm_num, by norm_num, by ring, by ring⟩
  -- A genuine polygon (`segments ≠ []`) has all its vertices on its boundary, so neither `P`
  -- nor `Q` (both off the boundary) is a vertex; then `constancy_of_notVertex` applies.
  have hvP : ∀ w ∈ poly.vertices, w ≠ P := by
    intro w hw hwP
    rcases vertex_mem_boundary hw with h | h
    · exact hPbf (hwP ▸ h)
    · exact hne h
  have hvQ : ∀ w ∈ poly.vertices, w ≠ Q := by
    intro w hw hwQ
    rcases vertex_mem_boundary hw with h | h
    · exact hQbf (hwQ ▸ h)
    · exact hne h
  exact constancy_of_notVertex hnd hPQ hvP hvQ hbf

end Polygons2
end
