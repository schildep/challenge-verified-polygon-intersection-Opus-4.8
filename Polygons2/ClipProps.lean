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

/-!
# Properties of the clipped intersection-boundary edge multiset `Mlist`.

This file proves the four target theorems about `Mlist poly1 poly2`.
-/

open Classical Set
noncomputable section
namespace Polygons2

/-! ## Boundary-freeness strictly between consecutive cut parameters -/

/-- If `a ≠ b`, the edge `⟨a,b⟩` is a poly1-edge, and the boundary intersection is finite,
then a parameter `u` strictly between two consecutive cut parameters of `⟨a,b⟩` against `poly2`
maps to a point off `poly2`'s boundary. -/
lemma seg_off_boundary_of_between {a b : Vector2D} (hab : a ≠ b)
    {poly1 poly2 : Polygon}
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {s t u : ℚ} (hs : s ∈ cutParams a b poly2) (ht : t ∈ cutParams a b poly2)
    (hbetween : ∀ v, s < v → v < t → v ∉ cutParams a b poly2)
    (hsu : s < u) (hut : u < t) :
    segPt a b u ∉ poly2.toBoundarySet := by
  intro hb
  -- u ∈ [0,1]
  have hs01 := cutParams_mem_Icc hs
  have ht01 := cutParams_mem_Icc ht
  have hu0 : 0 ≤ u := le_trans hs01.1 (le_of_lt hsu)
  have hu1 : u ≤ 1 := le_trans (le_of_lt hut) ht01.2
  -- so u ∈ cutSet, hence cutFinset, hence cutParams
  have hfinSet : Set.Finite (cutSet a b poly2) := cutSet_finite hab hsub hfin
  have humem : u ∈ cutParams a b poly2 := by
    rw [mem_cutParams_iff]
    right; right
    unfold cutFinset
    rw [dif_pos hfinSet, Set.Finite.mem_toFinset]
    exact ⟨hu0, hu1, hb⟩
  exact hbetween u hsu hut humem

/-! ## The kept piece containing a point -/

/-- A point of `⟨a,b⟩` at parameter `u` strictly inside a consecutive cut-interval `(s,t)`
lies on the segment `[segPt a b s, segPt a b t]`. -/
lemma segPt_mem_subpiece {a b : Vector2D} {s t u : ℚ}
    (hsu : s ≤ u) (hut : u ≤ t) :
    segPt a b u ∈ (LineSegment.mk (segPt a b s) (segPt a b t)).toSet := by
  -- write u as (1-λ)s + λ t
  rcases eq_or_lt_of_le (le_trans hsu hut) with hst | hst
  · -- s = t, so u = s = t
    have hus : u = s := le_antisymm (hst ▸ hut) hsu
    refine ⟨0, le_refl _, by norm_num, ?_, ?_⟩
    · simp [hus]
    · simp [hus]
  · set lam : ℚ := (u - s) / (t - s) with hlam
    have htms : 0 < t - s := by linarith
    have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one htms]; linarith
    refine ⟨lam, hlam0, hlam1, ?_, ?_⟩
    · simp only [segPt_x]
      rw [hlam]; field_simp; ring
    · simp only [segPt_y]
      rw [hlam]; field_simp; ring

/-! ## Adjacent cut parameters form a consecutive pair -/

/-- If `s < t` are both in the strictly-increasing list `cutParams a b poly` and nothing lies
strictly between, then `(s,t)` is a consecutive pair. -/
lemma consec_of_adjacent {a b : Vector2D} {poly : Polygon} {s t : ℚ}
    (hs : s ∈ cutParams a b poly) (ht : t ∈ cutParams a b poly) (hst : s < t)
    (hbetween : ∀ v, s < v → v < t → v ∉ cutParams a b poly) :
    (s, t) ∈ consecPairs (cutParams a b poly) := by
  set L := cutParams a b poly with hL
  have hpw := cutParams_pairwise_lt a b poly
  rw [List.pairwise_iff_getElem] at hpw
  obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.1 hs
  obtain ⟨j, hj, htj⟩ := List.mem_iff_getElem.1 ht
  -- i < j since L[i] = s < t = L[j]
  have hij : i < j := by
    rcases lt_trichotomy i j with h | h | h
    · exact h
    · subst h; rw [hsi] at htj; exact absurd htj (ne_of_lt hst)
    · have := hpw j i hj hi h; rw [hsi, htj] at this; linarith
  -- j = i+1 : else L[i+1] strictly between
  have hj1 : j = i + 1 := by
    by_contra hne
    have hi1 : i + 1 < j := by omega
    have h1 : i + 1 < L.length := by omega
    have hlo : s < L[i+1]'h1 := by rw [← hsi]; exact hpw i (i+1) hi h1 (by omega)
    have hhi : L[i+1]'h1 < t := by rw [← htj]; exact hpw (i+1) j h1 hj hi1
    exact hbetween (L[i+1]'h1) hlo hhi (List.getElem_mem _)
  -- build consecPairs membership
  unfold consecPairs
  rw [List.mem_iff_getElem]
  have hlenzip : i < (L.zip L.tail).length := by
    rw [List.length_zip, List.length_tail]; omega
  refine ⟨i, hlenzip, ?_⟩
  rw [List.getElem_zip, Prod.ext_iff]
  have h1 : i + 1 < L.length := by omega
  refine ⟨hsi, ?_⟩
  have htail : L.tail[i]'(by rw [List.length_tail]; omega) = L[i+1]'h1 :=
    List.getElem_tail _
  have hi1t : L[i+1]'h1 = t := by
    have : L[i+1]'h1 = L[j]'hj := by congr 1; omega
    rw [this, htj]
  rw [htail, hi1t]

/-! ## The kept piece membership -/

/-- A consecutive cut-pair `(s,t)` (with `s<t`, nothing strictly between) such that the open
interval is boundary-free; then `segPt a b s ≠ segPt a b t` and the midpoint shares the
interior status of any interior point of the open piece, so the piece is kept. -/
lemma piece_kept_of_interior {a b : Vector2D} (hab : a ≠ b)
    {poly1 poly2 : Polygon}
    (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2) (h2e : poly2.segments ≠ [])
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {s t u : ℚ} (hs : s ∈ cutParams a b poly2) (ht : t ∈ cutParams a b poly2)
    (hst : s < t) (hbetween : ∀ v, s < v → v < t → v ∉ cutParams a b poly2)
    (hsu : s ≤ u) (hut : u ≤ t) (hint : segPt a b u ∈ poly2.interior) :
    (segPt a b s, segPt a b t) ∈ clipEdge a b poly2 ∧
      segPt a b u ∈ (LineSegment.mk (segPt a b s) (segPt a b t)).toSet := by
  have hs01 := cutParams_mem_Icc hs
  have ht01 := cutParams_mem_Icc ht
  -- boundary-free open interval
  have hbf_open : ∀ v, s < v → v < t → segPt a b v ∉ poly2.toBoundarySet :=
    fun v hv1 hv2 => seg_off_boundary_of_between hab hsub hfin hs ht hbetween hv1 hv2
  -- midpoint param
  set m : ℚ := (s + t) / 2 with hm
  have hsm : s < m := by rw [hm]; linarith
  have hmt : m < t := by rw [hm]; linarith
  -- the closed segment between segPt u and segPt m is boundary-free
  have hmid_int : segPt a b m ∈ poly2.interior := by
    -- constancy between u and m: closed segment misses boundary
    rw [even_odd_constancy h2n h2e (P := segPt a b u) (Q := segPt a b m) ?_] at hint
    · exact hint
    · intro x hx
      -- x on segment [segPt u, segPt m]; it equals segPt a b w for some w in [min u m, max u m]
      obtain ⟨w, hw0, hw1, hxw⟩ := mem_seg_segPt hx
      -- x = (1-w) segPt u + w segPt m = segPt a b ((1-w)u + w m)
      have hxeq : x = segPt a b ((1 - w) * u + w * m) := by
        rw [hxw]; ext <;> simp only [segPt_x, segPt_y] <;> ring
      rw [hxeq]
      -- (1-w)u + w m : if w = 0 it is u (boundary-free via hint), else strictly in (s,t)
      set wp : ℚ := (1 - w) * u + w * m with hwp
      rcases eq_or_lt_of_le hw0 with hw0eq | hw0lt
      · -- w = 0 ⇒ wp = u
        have : wp = u := by rw [hwp, ← hw0eq]; ring
        rw [this]; exact fun hb => boundary_not_interior hb hint
      · -- w > 0 ⇒ s < wp < t
        have hlo : s < wp := by rw [hwp]; nlinarith [hsm, hsu, hw0lt, hw1]
        have hhi : wp < t := by rw [hwp]; nlinarith [hut, hmt, hw0lt, hw1]
        exact hbf_open _ hlo hhi
  -- the piece is kept
  have hne : segPt a b s ≠ segPt a b t := by
    intro h; exact absurd (segPt_injOn hab h) (ne_of_lt hst)
  constructor
  · -- membership in clipEdge: it's a consecutive pair
    unfold clipEdge
    rw [List.mem_filterMap]
    refine ⟨(s, t), ?_, ?_⟩
    · -- (s,t) ∈ consecPairs (cutParams a b poly2)
      exact consec_of_adjacent hs ht hst hbetween
    · simp only
      rw [if_pos ⟨by rw [← hm]; exact hmid_int, hne⟩]
  · exact segPt_mem_subpiece hsu hut

/-! ## Bracketing a parameter by consecutive cut parameters -/

/-- A strictly increasing list of rationals all of which lie in `[0,1]`, containing both `0`
and `1`; any `u ∈ [0,1]` is bracketed by a consecutive pair. -/
lemma bracket_consec (L : List ℚ) (hpw : L.Pairwise (· < ·))
    (hIcc : ∀ v ∈ L, 0 ≤ v ∧ v ≤ 1)
    (h0 : (0:ℚ) ∈ L) (h1 : (1:ℚ) ∈ L) {u : ℚ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ i : ℕ, ∃ (h : i + 1 < L.length), L[i] ≤ u ∧ u ≤ L[i+1] := by
  rw [List.pairwise_iff_getElem] at hpw
  obtain ⟨i0, hi0, hi0v⟩ := List.mem_iff_getElem.1 h0
  obtain ⟨i1, hi1, hi1v⟩ := List.mem_iff_getElem.1 h1
  -- The set of indices j with L[j] ≤ u is nonempty (contains i0).
  set S : Finset ℕ := (Finset.range L.length).filter (fun j => decide (∃ h : j < L.length, L[j] ≤ u)) with hS
  have memS : ∀ j, j ∈ S ↔ ∃ h : j < L.length, L[j] ≤ u := by
    intro j; rw [hS, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h, hu⟩; exact ⟨h, h, hu⟩
  have hi0S : i0 ∈ S := (memS i0).2 ⟨hi0, by rw [hi0v]; exact hu0⟩
  have hSne : S.Nonempty := ⟨i0, hi0S⟩
  set i := S.max' hSne with hi
  obtain ⟨hilt, hiu⟩ := (memS i).1 (S.max'_mem hSne)
  -- i is not the last index, because the last index has value 1 (max element) and 1 ≥ u; if
  -- u < 1 then i < lastindex; if u = 1, we need to argue i+1 exists.  We show: i+1 < length by
  -- ruling out that i is the global maximum index unless u = 1, and even then i can't be the
  -- index of value 1 while being the last (then use that all values ≤ 1, so value-1 index is
  -- last, giving the bracket at i, i+1=last only when there are ≥2 elements; handle u=1).
  -- Key: the last index `n-1` has the maximal value, which is ≥ 1 (since 1 ∈ L), hence = 1.
  have hlen_pos : 0 < L.length := by
    cases L with
    | nil => simp at h0
    | cons _ _ => simp
  set n := L.length with hn
  have hlast_val : L[n-1]'(by omega) = 1 := by
    have hle1 : L[n-1]'(by omega) ≤ 1 := (hIcc _ (List.getElem_mem _)).2
    have hge : (1:ℚ) ≤ L[n-1]'(by omega) := by
      rcases lt_or_eq_of_le (show i1 ≤ n-1 by omega) with hlt | heq
      · have := hpw i1 (n-1) hi1 (by omega) hlt; rw [hi1v] at this; linarith
      · have : L[i1] = L[n-1]'(by omega) := by congr 1
        rw [hi1v] at this; linarith
    linarith
  -- n ≥ 2 (since 0 ≠ 1 are both present)
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hn1 : n = 1 := by omega
    have hi00 : i0 = i1 := by omega
    have e0 : L[i0] = L[i1] := by congr 1
    rw [hi0v, hi1v] at e0; norm_num at e0
  rcases lt_or_eq_of_le hu1 with hu_lt | hu_eq
  · -- u < 1 = L[n-1]; so i < n-1 (as L[n-1] = 1 > u means n-1 ∉ S, so i ≠ n-1)
    have hi_ne : i ≠ n - 1 := by
      intro heq
      have hli : L[i] = L[n-1]'(by omega) := by congr 1
      rw [hli, hlast_val] at hiu; linarith
    have hi1_lt : i + 1 < n := by omega
    refine ⟨i, hi1_lt, hiu, ?_⟩
    by_contra hcon
    push_neg at hcon
    have : (i+1) ∈ S := (memS (i+1)).2 ⟨hi1_lt, le_of_lt hcon⟩
    have := S.le_max' (i+1) this
    omega
  · -- u = 1; bracket by (n-2, n-1)
    subst hu_eq
    refine ⟨n - 2, by omega, ?_, ?_⟩
    · exact (hIcc _ (List.getElem_mem _)).2
    · have : L[(n-2)+1]'(by omega) = L[n-1]'(by omega) := by congr 1; omega
      rw [this, hlast_val]

/-! ## Existence of a kept piece through an interior point -/

/-- A point `q` on the poly1-edge `⟨a,b⟩` that lies in `poly2.interior` lies on some kept
piece of `clipEdge a b poly2`. -/
lemma exists_clipEdge_through {a b : Vector2D} (hab : a ≠ b)
    {poly1 poly2 : Polygon}
    (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2) (h2e : poly2.segments ≠ [])
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {q : Vector2D} (hq : q ∈ (LineSegment.mk a b).toSet) (hint : q ∈ poly2.interior) :
    ∃ e ∈ clipEdge a b poly2, q ∈ (LineSegment.mk e.1 e.2).toSet := by
  -- q = segPt a b u
  obtain ⟨u, hu0, hu1, hqu⟩ := mem_seg_segPt hq
  subst hqu
  -- q is in interior, hence off poly2's boundary
  have hqbf : segPt a b u ∉ poly2.toBoundarySet := fun hb => boundary_not_interior hb hint
  -- bracket u by consecutive cut params
  obtain ⟨i, hilen, hle, hge⟩ := bracket_consec (cutParams a b poly2)
    (cutParams_pairwise_lt a b poly2) (fun v hv => cutParams_mem_Icc hv)
    (zero_mem_cutParams a b poly2) (one_mem_cutParams a b poly2) hu0 hu1
  set L := cutParams a b poly2 with hL
  set s := L[i] with hs_def
  set t := L[i+1] with ht_def
  have hsmem : s ∈ L := List.getElem_mem _
  have htmem : t ∈ L := List.getElem_mem _
  have hsu : s ≤ u := hle
  have hut : u ≤ t := hge
  -- s < t (strictly increasing list)
  have hst : s < t := by
    have hpw := cutParams_pairwise_lt a b poly2
    rw [List.pairwise_iff_getElem] at hpw
    exact hpw i (i+1) (by omega) hilen (by omega)
  -- nothing strictly between s and t
  have hbetween : ∀ v, s < v → v < t → v ∉ L := by
    intro v hv1 hv2 hvmem
    obtain ⟨k, hk, hvk⟩ := List.mem_iff_getElem.1 hvmem
    have hpw := cutParams_pairwise_lt a b poly2
    rw [List.pairwise_iff_getElem] at hpw
    -- hvk : L[k] = v;  s = L[i], t = L[i+1]
    rcases lt_trichotomy k i with hki | hki | hki
    · have h := hpw k i hk (by omega) hki
      -- L[k] < L[i] = s, but v = L[k] and s < v
      rw [hvk] at h; exact absurd (lt_trans hv1 h) (lt_irrefl _)
    · subst hki; rw [← hvk] at hv1; exact absurd hv1 (lt_irrefl _)
    · rcases lt_trichotomy k (i+1) with hk2 | hk2 | hk2
      · omega
      · subst hk2; rw [← hvk] at hv2; exact absurd hv2 (lt_irrefl _)
      · have h := hpw (i+1) k hilen hk hk2
        rw [hvk] at h; exact absurd (lt_trans hv2 h) (lt_irrefl _)
  obtain ⟨hkept, hmem⟩ := piece_kept_of_interior hab h2n h2e hsub hfin hsmem htmem hst hbetween
    hsu hut hint
  exact ⟨(segPt a b s, segPt a b t), hkept, hmem⟩

/-! ## Theorem (2): crossing count equals inside-crossings -/

/-- For `a ≠ b` and `s ≤ t`, a point `segPt a b u` lies on the sub-piece `[segPt a b s,
segPt a b t]` iff `u ∈ [s,t]`. -/
lemma segPt_mem_subpiece_iff {a b : Vector2D} (hab : a ≠ b) {s t u : ℚ} (hst : s ≤ t) :
    segPt a b u ∈ (LineSegment.mk (segPt a b s) (segPt a b t)).toSet ↔ (s ≤ u ∧ u ≤ t) := by
  constructor
  · rintro ⟨w, hw0, hw1, hx, hy⟩
    -- segPt a b u = (1-w) segPt s + w segPt t = segPt at (1-w)s + w t
    have hueq : u = (1 - w) * s + w * t := by
      have hxx : (1 - u) * a.x + u * b.x = (1-w) * ((1-s)*a.x + s*b.x) + w*((1-t)*a.x+t*b.x) := by
        simpa [segPt] using hx
      have hyy : (1 - u) * a.y + u * b.y = (1-w) * ((1-s)*a.y + s*b.y) + w*((1-t)*a.y+t*b.y) := by
        simpa [segPt] using hy
      -- subtract: (u - ((1-w)s+wt)) (b - a) = 0
      have ex : (u - ((1-w)*s + w*t)) * (b.x - a.x) = 0 := by linear_combination hxx
      have ey : (u - ((1-w)*s + w*t)) * (b.y - a.y) = 0 := by linear_combination hyy
      by_contra hne
      have hd : u - ((1-w)*s + w*t) ≠ 0 := fun h => hne (by linarith [sub_eq_zero.1 h])
      have hbx : b.x - a.x = 0 := by rcases mul_eq_zero.1 ex with h|h; exacts [absurd h hd, h]
      have hby : b.y - a.y = 0 := by rcases mul_eq_zero.1 ey with h|h; exacts [absurd h hd, h]
      exact hab (by ext <;> [linarith; linarith])
    constructor
    · rw [hueq]; nlinarith [hw0, hw1, hst]
    · rw [hueq]; nlinarith [hw0, hw1, hst]
  · rintro ⟨h1, h2⟩
    exact segPt_mem_subpiece h1 h2

/-- If a predicate holds at exactly one index (and only when a fixed flag `b` is set), the count
is `1` (if `b`) or `0`. -/
lemma countP_unique_index {α : Type*} (l : List α) (P : α → Bool) (i₀ : ℕ) (b : Bool)
    (hi₀ : i₀ < l.length)
    (h : ∀ j (hj : j < l.length), P (l[j]) = true ↔ (j = i₀ ∧ b = true)) :
    l.countP P = if b then 1 else 0 := by
  -- Reduce to the case b = true; if b = false predicate is never satisfied.
  by_cases hb : b = true
  · subst hb
    -- predicate true exactly at index i₀
    have hkey : ∀ j (hj : j < l.length), P (l[j]) = true ↔ j = i₀ := by
      intro j hj; rw [h j hj]; simp
    clear h
    induction l generalizing i₀ with
    | nil => simp at hi₀
    | cons a t ih =>
      rw [List.countP_cons]
      have hhead : P a = true ↔ i₀ = 0 := by
        have h0 := hkey 0 (by simp)
        simp only [List.getElem_cons_zero] at h0
        rw [h0]; exact eq_comm
      by_cases hi0 : i₀ = 0
      · have htail : t.countP P = 0 := by
          rw [List.countP_eq_zero]
          intro x hx hPx
          obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.1 hx
          have := hkey (j+1) (by simp; omega)
          simp only [List.getElem_cons_succ] at this
          rw [← hxj] at hPx; have := this.1 hPx; omega
        rw [htail, if_pos (hhead.2 hi0)]; simp
      · have hhno : P a ≠ true := fun h0 => hi0 (hhead.1 h0)
        have htc : t.countP P = 1 := by
          have := ih (i₀-1) (by simp at hi₀; omega) (by
            intro j hj
            have := hkey (j+1) (by simp; omega)
            simp only [List.getElem_cons_succ] at this
            rw [this]; omega)
          simpa using this
        rw [htc]; simp [hhno]
  · have hbf : b = false := by cases b <;> simp_all
    subst hbf
    simp only [Bool.false_eq_true, if_false]
    rw [List.countP_eq_zero]
    intro x hx hPx
    obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.1 hx
    have := (h j hj).1 (by rw [← hxj] at hPx; exact hPx)
    exact absurd this.2 (by simp)

/-- Counting consecutive pairs of a strictly increasing list whose closed interval contains a
fixed `u` not equal to any element: exactly one such pair, weighted by a predicate `K` that holds
for it iff `kept`. -/
lemma countP_consecPairs_bracket (L : List ℚ) (hpw : L.Pairwise (· < ·))
    (K : ℚ × ℚ → Bool) {u : ℚ} {i : ℕ} (hi : i + 1 < L.length)
    (hlo : L[i] < u) (hhi : u < L[i+1])
    (hunot : ∀ v ∈ L, v ≠ u) :
    (consecPairs L).countP (fun st => decide (st.1 ≤ u ∧ u ≤ st.2) && K st)
      = (if K (L[i], L[i+1]'hi) then 1 else 0) := by
  -- consecPairs L = L.zip L.tail; index it.
  -- We show the predicate holds for the i-th pair (= (L[i], L[i+1])) iff K, and for no other.
  have hpwget : ∀ (a b : ℕ) (_ : a < L.length) (_ : b < L.length), a < b → L[a] < L[b] := by
    rw [List.pairwise_iff_getElem] at hpw; intro a b ha hb hab; exact hpw a b ha hb hab
  -- The j-th consecutive pair is (L[j], L[j+1]).
  have hlen : (consecPairs L).length = L.length - 1 := by
    unfold consecPairs; rw [List.length_zip, List.length_tail]; omega
  have hget : ∀ j (hj : j < (consecPairs L).length),
      (consecPairs L)[j] = (L[j]'(by rw [hlen] at hj; omega), L[j+1]'(by rw [hlen] at hj; omega)) := by
    intro j hj
    unfold consecPairs
    rw [List.getElem_zip]
    have : L.tail[j]'(by rw [List.length_tail]; rw [hlen] at hj; omega) = L[j+1]'(by rw [hlen] at hj; omega) :=
      List.getElem_tail _
    rw [Prod.ext_iff]; exact ⟨rfl, this⟩
  -- predicate on index j
  set Pred : ℚ × ℚ → Bool := fun st => decide (st.1 ≤ u ∧ u ≤ st.2) && K st with hPred
  -- prove: for j ≠ i, Pred ((consecPairs L)[j]) = false; for j = i, Pred = K(L[i],L[i+1]).
  have key : ∀ j (hj : j < (consecPairs L).length),
      (Pred ((consecPairs L)[j]) = true) ↔ (j = i ∧ K (L[i], L[i+1]'hi) = true) := by
    intro j hj
    rw [hget j hj, hPred]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hjlen : j + 1 < L.length := by rw [hlen] at hj; omega
    constructor
    · rintro ⟨⟨hle1, hle2⟩, hK⟩
      -- L[j] ≤ u ≤ L[j+1], and L[i] < u < L[i+1]; strictly increasing ⇒ j = i
      have hji : j = i := by
        rcases lt_trichotomy j i with h | h | h
        · -- j < i ⇒ j+1 ≤ i ⇒ L[j+1] ≤ L[i] < u, contradicting u ≤ L[j+1]
          rcases lt_or_eq_of_le (show j + 1 ≤ i by omega) with h2 | h2
          · have := hpwget (j+1) i hjlen (by omega) h2; linarith
          · -- j+1 = i ⇒ L[j+1] = L[i] < u, but u ≤ L[j+1]
            have : L[j+1]'hjlen = L[i] := by congr 1
            rw [this] at hle2; linarith
        · exact h
        · -- j > i ⇒ i+1 ≤ j ⇒ u < L[i+1] ≤ L[j] ≤ u
          rcases lt_or_eq_of_le (show i + 1 ≤ j by omega) with h2 | h2
          · have hlt := hpwget (i+1) j hi (by omega) h2
            have e : (L[i+1]'hi) = L[i+1] := rfl
            rw [e] at hhi; linarith
          · have e : (L[i+1]'hi) = L[j] := by congr 1
            rw [e] at hhi; linarith
      refine ⟨hji, ?_⟩
      have e3 : K (L[j], L[j+1]'hjlen) = K (L[i], L[i+1]'hi) := by
        subst hji; rfl
      rw [e3] at hK; exact hK
    · rintro ⟨hji, hK⟩
      subst hji
      exact ⟨⟨le_of_lt hlo, le_of_lt hhi⟩, hK⟩
  -- count via the index characterization
  have hilen : i < (consecPairs L).length := by rw [hlen]; omega
  exact countP_unique_index (consecPairs L) Pred i (K (L[i], L[i+1]'hi)) hilen key

/-- `countP` over a `filterMap`. -/
lemma countP_filterMap {α β : Type*} (g : α → Option β) (P : β → Bool) (l : List α) :
    (l.filterMap g).countP P
      = l.countP (fun a => match g a with | some b => P b | none => false) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons]
    cases hg : g a with
    | none => simp [hg, ih]
    | some b => rw [List.countP_cons, ih, List.countP_cons]; simp [hg]

/-- If `r` does not cross the edge `⟨a,b⟩`, it crosses none of its clipped pieces. -/
lemma clipEdge_countP_cross_zero {a b : Vector2D} {poly2 : Polygon} {r : Ray}
    (hnc : ¬ rayIntersectsSegment r (LineSegment.mk a b)) :
    (clipEdge a b poly2).countP
      (fun pc => decide (rayIntersectsSegment r (LineSegment.mk pc.1 pc.2))) = 0 := by
  rw [List.countP_eq_zero]
  intro pc hpc
  obtain ⟨s, t, hs, ht, _, _, _, _, hpeq⟩ := mem_clipEdge hpc
  simp only [decide_eq_true_eq]
  intro hcross
  apply hnc
  obtain ⟨z, hzr, hzs⟩ := hcross
  rw [hpeq] at hzs
  exact ⟨z, hzr, subpiece_subset (cutParams_mem_Icc hs) (cutParams_mem_Icc ht) hzs⟩

/-- The per-edge crossing count for a poly1-edge, with `q = crossingPoint r e` off `poly2`'s
boundary. -/
lemma clipEdge_countP_cross {a b : Vector2D} (hab : a ≠ b)
    {poly1 poly2 : Polygon}
    (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2) (h2e : poly2.segments ≠ [])
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {r : Ray} (h1off : a ∉ r.toSet) (h2off : b ∉ r.toSet)
    (hcross : rayIntersectsSegment r (LineSegment.mk a b))
    (hqbf : crossingPoint r (LineSegment.mk a b) ∉ poly2.toBoundarySet) :
    (clipEdge a b poly2).countP
      (fun pc => decide (rayIntersectsSegment r (LineSegment.mk pc.1 pc.2)))
      = if crossingPoint r (LineSegment.mk a b) ∈ poly2.interior then 1 else 0 := by
  obtain ⟨hqr, hqs⟩ := crossingPoint_mem hcross
  set q := crossingPoint r (LineSegment.mk a b) with hqdef
  -- q's edge param
  obtain ⟨uq, huq0, huq1, hquq⟩ := mem_seg_segPt hqs
  -- r ∩ e = {q}
  have hsing := ray_seg_inter_singleton r (LineSegment.mk a b) hab h1off h2off hcross
  -- For any piece pc ⊆ e, r crosses pc ↔ q ∈ pc.toSet
  have hcross_iff : ∀ pc : Vector2D × Vector2D, pc ∈ clipEdge a b poly2 →
      (rayIntersectsSegment r (LineSegment.mk pc.1 pc.2) ↔ q ∈ (LineSegment.mk pc.1 pc.2).toSet) := by
    intro pc hpc
    obtain ⟨s, t, hs, ht, _, _, _, _, hpeq⟩ := mem_clipEdge hpc
    have hpcsub : (LineSegment.mk pc.1 pc.2).toSet ⊆ (LineSegment.mk a b).toSet := by
      rw [hpeq]; exact subpiece_subset (cutParams_mem_Icc hs) (cutParams_mem_Icc ht)
    constructor
    · rintro ⟨z, hzr, hzs⟩
      have hz_eq : z = q := by
        have : z ∈ r.toSet ∩ (LineSegment.mk a b).toSet := ⟨hzr, hpcsub hzs⟩
        rw [hsing] at this; exact this
      rw [← hz_eq]; exact hzs
    · intro hqpc
      exact ⟨q, hqr, hqpc⟩
  -- rewrite countP over the cross predicate to the "q ∈ pc" predicate
  have hstep1 : (clipEdge a b poly2).countP
      (fun pc => decide (rayIntersectsSegment r (LineSegment.mk pc.1 pc.2)))
      = (clipEdge a b poly2).countP (fun pc => decide (q ∈ (LineSegment.mk pc.1 pc.2).toSet)) := by
    apply List.countP_congr
    intro pc hpc
    simp only [decide_eq_true_eq]
    exact hcross_iff pc hpc
  rw [hstep1]
  -- express over consecPairs via countP_filterMap
  have hfm : (clipEdge a b poly2).countP (fun pc => decide (q ∈ (LineSegment.mk pc.1 pc.2).toSet))
      = (consecPairs (cutParams a b poly2)).countP
          (fun st => decide (st.1 ≤ uq ∧ uq ≤ st.2)
            && decide (segPt a b ((st.1 + st.2)/2) ∈ poly2.interior ∧ segPt a b st.1 ≠ segPt a b st.2)) := by
    unfold clipEdge
    rw [countP_filterMap]
    apply List.countP_congr
    intro st hst
    -- the g for clipEdge
    have hsle : st.1 ≤ st.2 := by
      obtain ⟨i', hi', heq⟩ := mem_consecPairs hst
      have hpw := cutParams_pairwise_lt a b poly2
      rw [List.pairwise_iff_getElem] at hpw
      rw [heq]; exact le_of_lt (hpw i' (i'+1) (by omega) hi' (by omega))
    have hqiff : (q ∈ (LineSegment.mk (segPt a b st.1) (segPt a b st.2)).toSet)
        ↔ (st.1 ≤ uq ∧ uq ≤ st.2) := by
      rw [hquq]; exact segPt_mem_subpiece_iff hab hsle
    by_cases hk : segPt a b ((st.1 + st.2)/2) ∈ poly2.interior ∧ segPt a b st.1 ≠ segPt a b st.2
    · simp only [if_pos hk]
      rw [decide_eq_true hk, Bool.and_true, decide_eq_true_eq, decide_eq_true_eq]
      exact hqiff
    · simp only [if_neg hk]
      rw [decide_eq_false hk, Bool.and_false]
  rw [hfm]
  -- Set up the bracket of uq.
  set L := cutParams a b poly2 with hL
  have hpwL : ∀ (x y : ℕ) (_ : x < L.length) (_ : y < L.length), x < y → L[x] < L[y] := by
    have h := cutParams_pairwise_lt a b poly2
    rw [List.pairwise_iff_getElem] at h
    intro x y hx hy hxy; exact h x y (by rw [hL] at hx; exact hx) (by rw [hL] at hy; exact hy) hxy
  -- q ≠ a, q ≠ b ⇒ uq ≠ 0, uq ≠ 1
  have hqa : q = a → False := by
    intro h; exact h1off (by rw [← h]; exact hqr)
  have hqb : q = b → False := by
    intro h; exact h2off (by rw [← h]; exact hqr)
  have huq_ne0 : uq ≠ 0 := by
    intro h; apply hqa; rw [hquq, h]; simp
  have huq_ne1 : uq ≠ 1 := by
    intro h; apply hqb; rw [hquq, h]; simp
  -- uq is not a cut param (else q on poly2 boundary)
  have huq_notmem : ∀ v ∈ L, v ≠ uq := by
    intro v hv hvuq
    rw [mem_cutParams_iff] at hv
    rcases hv with h | h | h
    · exact huq_ne0 (by rw [← hvuq, h])
    · exact huq_ne1 (by rw [← hvuq, h])
    · -- v ∈ cutFinset ⇒ segPt a b v ∈ poly2.boundary = q ∈ boundary
      apply hqbf
      rw [hquq, ← hvuq]
      unfold cutFinset at h
      split_ifs at h with hfinSet
      · rw [Set.Finite.mem_toFinset] at h; exact h.2.2
      · simp at h
  -- bracket uq
  obtain ⟨i, hilen, hle, hge⟩ := bracket_consec L (cutParams_pairwise_lt a b poly2)
    (fun v hv => cutParams_mem_Icc hv) (zero_mem_cutParams a b poly2) (one_mem_cutParams a b poly2)
    huq0 huq1
  have hLi : L[i] < uq := lt_of_le_of_ne hle (huq_notmem _ (List.getElem_mem _))
  have hLi1 : uq < L[i+1] := lt_of_le_of_ne hge (Ne.symm (huq_notmem _ (List.getElem_mem _)))
  -- K characterization at the bracketing pair
  have hKchar : (decide (segPt a b ((L[i] + L[i+1]'hilen)/2) ∈ poly2.interior
        ∧ segPt a b L[i] ≠ segPt a b (L[i+1]'hilen)))
      = decide (q ∈ poly2.interior) := by
    -- both conjuncts; segPt L[i] ≠ segPt L[i+1]; midpoint ∈ int ↔ q ∈ int
    have hne : segPt a b L[i] ≠ segPt a b (L[i+1]'hilen) := by
      intro h
      exact absurd (segPt_injOn hab h) (ne_of_lt (hpwL i (i+1) (by omega) hilen (by omega)))
    -- boundary-free open interval
    have hbetween : ∀ v, L[i] < v → v < L[i+1]'hilen → v ∉ L := by
      intro v hv1 hv2 hvmem
      obtain ⟨k, hk, hvk⟩ := List.mem_iff_getElem.1 hvmem
      rcases lt_trichotomy k i with hki | hki | hki
      · have h := hpwL k i hk (by omega) hki; rw [hvk] at h; linarith
      · subst hki; rw [← hvk] at hv1; exact absurd hv1 (lt_irrefl _)
      · rcases lt_trichotomy k (i+1) with hk2 | hk2 | hk2
        · omega
        · subst hk2; rw [← hvk] at hv2; exact absurd hv2 (lt_irrefl _)
        · have h := hpwL (i+1) k hilen hk hk2; rw [hvk] at h; linarith
    have hbf_open : ∀ v, L[i] < v → v < L[i+1]'hilen → segPt a b v ∉ poly2.toBoundarySet :=
      fun v hv1 hv2 => seg_off_boundary_of_between hab hsub hfin
        (List.getElem_mem _) (List.getElem_mem _) hbetween hv1 hv2
    -- midpoint param m
    set m : ℚ := (L[i] + L[i+1]'hilen)/2 with hm
    have hsm : L[i] < m := by rw [hm]; linarith
    have hmt : m < L[i+1]'hilen := by rw [hm]; linarith
    -- constancy: segPt m ∈ int ↔ q ∈ int (q = segPt uq)
    have hconst : segPt a b m ∈ poly2.interior ↔ q ∈ poly2.interior := by
      rw [hquq, even_odd_constancy h2n h2e (P := segPt a b m) (Q := segPt a b uq) ?_]
      intro x hx
      obtain ⟨w, hw0, hw1, hxw⟩ := mem_seg_segPt hx
      have hxeq : x = segPt a b ((1 - w) * m + w * uq) := by
        rw [hxw]; ext <;> simp only [segPt_x, segPt_y] <;> ring
      rw [hxeq]
      -- (1-w)m + w uq ∈ (L[i], L[i+1])
      have hlo' : L[i] < (1 - w) * m + w * uq := by nlinarith [hsm, hLi, hw0, hw1]
      have hhi' : (1 - w) * m + w * uq < L[i+1]'hilen := by nlinarith [hmt, hLi1, hw0, hw1]
      exact hbf_open _ hlo' hhi'
    rw [decide_eq_decide]
    constructor
    · rintro ⟨h1, _⟩; exact hconst.1 h1
    · intro hqint; exact ⟨hconst.2 hqint, hne⟩
  -- apply the bracket counting lemma
  rw [countP_consecPairs_bracket L (cutParams_pairwise_lt a b poly2)
    (fun st => decide (segPt a b ((st.1 + st.2)/2) ∈ poly2.interior
      ∧ segPt a b st.1 ≠ segPt a b st.2)) hilen hLi hLi1 huq_notmem]
  simp only at hKchar ⊢
  rw [hKchar]
  simp [decide_eq_true_eq]

/-- Per-edge count packaged as the inside-crossing indicator. -/
lemma clipEdge_countP_eq_indicator {a b : Vector2D} (hab : a ≠ b)
    {poly1 poly2 : Polygon}
    (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2) (h2e : poly2.segments ≠ [])
    (hsub : (LineSegment.mk a b).toSet ⊆ poly1.toBoundarySet)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {r : Ray} (h1off : a ∉ r.toSet) (h2off : b ∉ r.toSet)
    (hS : ∀ x ∈ r.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False) :
    (clipEdge a b poly2).countP
      (fun pc => decide (rayIntersectsSegment r (LineSegment.mk pc.1 pc.2)))
      = if (rayIntersectsSegment r (LineSegment.mk a b)
          ∧ crossingPoint r (LineSegment.mk a b) ∈ poly2.interior) then 1 else 0 := by
  by_cases hc : rayIntersectsSegment r (LineSegment.mk a b)
  · -- q off poly2 boundary via hS
    obtain ⟨hqr, hqs⟩ := crossingPoint_mem hc
    have hqbf : crossingPoint r (LineSegment.mk a b) ∉ poly2.toBoundarySet := by
      intro hb2
      exact hS _ hqr (hsub hqs) hb2
    rw [clipEdge_countP_cross hab h2n h2e hsub hfin h1off h2off hc hqbf]
    simp only [hc, true_and]
  · rw [clipEdge_countP_cross_zero hc, if_neg (by tauto)]

/-- `countP` distributes over `flatMap` as a sum. -/
lemma countP_flatMap {α β : Type*} (f : α → List β) (P : β → Bool) (l : List α) :
    (l.flatMap f).countP P = (l.map (fun a => (f a).countP P)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.flatMap_cons, List.countP_append, ih, List.map_cons, List.sum_cons]

/-- `countP` as a sum of indicators. -/
lemma countP_eq_sum_indicator {α : Type*} (P : α → Bool) (l : List α) :
    l.countP P = (l.map (fun a => if P a then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
    rcases Bool.eq_false_or_eq_true (P a) with h | h <;> rw [h] <;> simp <;> omega

theorem Mlist_countP_eq_insideCrossings (poly1 poly2 : Polygon) (r : Ray)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hav1 : rayAvoidsVertices r poly1) (hav2 : rayAvoidsVertices r poly2)
    (hS : ∀ x ∈ r.toSet, x ∈ poly1.toBoundarySet → x ∈ poly2.toBoundarySet → False)
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet)) :
    (Mlist poly1 poly2).countP (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩))
      = insideCrossings r poly1 poly2 := by
  have hS' : ∀ x ∈ r.toSet, x ∈ poly2.toBoundarySet → x ∈ poly1.toBoundarySet → False :=
    fun x hx h2 h1 => hS x hx h1 h2
  have hfin' : Set.Finite (poly2.toBoundarySet ∩ poly1.toBoundarySet) := by
    rw [Set.inter_comm]; exact hfin
  -- per-edge for poly1
  have hpoly1 : (poly1.segments.flatMap (fun e => clipEdge e.p1 e.p2 poly2)).countP
      (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩))
      = poly1.segments.countP
        (fun e => decide (rayIntersectsSegment r e ∧ crossingPoint r e ∈ poly2.interior)) := by
    rw [countP_flatMap, countP_eq_sum_indicator
      (fun e => decide (rayIntersectsSegment r e ∧ crossingPoint r e ∈ poly2.interior))]
    apply congrArg
    apply List.map_congr_left
    intro e he
    have hab : e.p1 ≠ e.p2 := h1n e he
    have hsub : (LineSegment.mk e.p1 e.p2).toSet ⊆ poly1.toBoundarySet :=
      fun x hx => ⟨e, he, by cases e; exact hx⟩
    obtain ⟨h1off, h2off⟩ := seg_endpoints_off_ray hav1 he
    rw [clipEdge_countP_eq_indicator hab h2n h2e hsub hfin h1off h2off hS]
    -- match ⟨e.p1,e.p2⟩ with e
    have hee : LineSegment.mk e.p1 e.p2 = e := by cases e; rfl
    rw [hee]
    simp only [decide_eq_true_eq]
  -- per-edge for poly2
  have hpoly2 : (poly2.segments.flatMap (fun f => clipEdge f.p1 f.p2 poly1)).countP
      (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩))
      = poly2.segments.countP
        (fun f => decide (rayIntersectsSegment r f ∧ crossingPoint r f ∈ poly1.interior)) := by
    rw [countP_flatMap, countP_eq_sum_indicator
      (fun f => decide (rayIntersectsSegment r f ∧ crossingPoint r f ∈ poly1.interior))]
    apply congrArg
    apply List.map_congr_left
    intro f hf
    have hab : f.p1 ≠ f.p2 := h2n f hf
    have hsub : (LineSegment.mk f.p1 f.p2).toSet ⊆ poly2.toBoundarySet :=
      fun x hx => ⟨f, hf, by cases f; exact hx⟩
    obtain ⟨h1off, h2off⟩ := seg_endpoints_off_ray hav2 hf
    rw [clipEdge_countP_eq_indicator hab h1n h1e hsub hfin' h1off h2off hS']
    have hff : LineSegment.mk f.p1 f.p2 = f := by cases f; rfl
    rw [hff]
    simp only [decide_eq_true_eq]
  -- assemble
  unfold Mlist insideCrossings
  rw [List.countP_append, hpoly1, hpoly2]

/-! ## Theorem (3): a boundary point inside the other polygon lies on an M-edge -/

/-- A clipped piece of a poly1-edge belongs to `Mlist`. -/
lemma clipEdge_poly1_mem_Mlist {poly1 poly2 : Polygon} {e : LineSegment}
    (he : e ∈ poly1.segments) {pc : Vector2D × Vector2D}
    (hpc : pc ∈ clipEdge e.p1 e.p2 poly2) :
    pc ∈ Mlist poly1 poly2 := by
  unfold Mlist
  rw [List.mem_append]; left
  rw [List.mem_flatMap]
  exact ⟨e, he, hpc⟩

/-- A clipped piece of a poly2-edge belongs to `Mlist`. -/
lemma clipEdge_poly2_mem_Mlist {poly1 poly2 : Polygon} {f : LineSegment}
    (hf : f ∈ poly2.segments) {pc : Vector2D × Vector2D}
    (hpc : pc ∈ clipEdge f.p1 f.p2 poly1) :
    pc ∈ Mlist poly1 poly2 := by
  unfold Mlist
  rw [List.mem_append]; right
  rw [List.mem_flatMap]
  exact ⟨f, hf, hpc⟩

theorem Mlist_mem_of_inside (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p : Vector2D} (hpA : p ∈ poly1.toBoundarySet) (hpB : p ∈ poly2.interior) :
    ∃ e ∈ Mlist poly1 poly2, p ∈ (LineSegment.mk e.1 e.2).toSet := by
  obtain ⟨e, he, hpe⟩ := hpA
  have hab : e.p1 ≠ e.p2 := h1n e he
  have hsub : (LineSegment.mk e.p1 e.p2).toSet ⊆ poly1.toBoundarySet := by
    intro x hx; exact ⟨e, he, by cases e; exact hx⟩
  have hpe' : p ∈ (LineSegment.mk e.p1 e.p2).toSet := by cases e; exact hpe
  obtain ⟨pc, hpc, hmem⟩ := exists_clipEdge_through hab h2n h2e hsub hfin hpe' hpB
  exact ⟨pc, clipEdge_poly1_mem_Mlist he hpc, hmem⟩

theorem Mlist_mem_of_inside' (poly1 poly2 : Polygon)
    (h1n : ∀ s ∈ poly1.segments, s.p1 ≠ s.p2) (h2n : ∀ s ∈ poly2.segments, s.p1 ≠ s.p2)
    (h1e : poly1.segments ≠ []) (h2e : poly2.segments ≠ [])
    (hfin : Set.Finite (poly1.toBoundarySet ∩ poly2.toBoundarySet))
    {p : Vector2D} (hpB : p ∈ poly2.toBoundarySet) (hpA : p ∈ poly1.interior) :
    ∃ e ∈ Mlist poly1 poly2, p ∈ (LineSegment.mk e.1 e.2).toSet := by
  obtain ⟨f, hf, hpf⟩ := hpB
  have hab : f.p1 ≠ f.p2 := h2n f hf
  have hsub : (LineSegment.mk f.p1 f.p2).toSet ⊆ poly2.toBoundarySet := by
    intro x hx; exact ⟨f, hf, by cases f; exact hx⟩
  have hpf' : p ∈ (LineSegment.mk f.p1 f.p2).toSet := by cases f; exact hpf
  have hfin' : Set.Finite (poly2.toBoundarySet ∩ poly1.toBoundarySet) := by
    rw [Set.inter_comm]; exact hfin
  obtain ⟨pc, hpc, hmem⟩ := exists_clipEdge_through hab h1n h1e hsub hfin' hpf' hpA
  exact ⟨pc, clipEdge_poly2_mem_Mlist hf hpc, hmem⟩

/-!
## Status of theorems (1) `Mlist_even_degree` and (4) `S_subset_Mlist`

These two are **not** included here. Both reduce to the **one-crossing FLIP lemma**:

> For points `P, Q` collinear on a polygon edge with the open segment `(P,Q)` meeting `poly`'s
> boundary at exactly one transversal point `c` (on a single edge `f`, `c` not a vertex), then
> `P ∈ poly.interior ↔ Q ∉ poly.interior`.

The infrastructure built above (`exists_clipEdge_through`, `piece_kept_of_interior`,
`clipEdge_countP_cross`, the bracketing/counting lemmas) directly supplies everything needed
*around* the flip:

* (4) `S_subset_Mlist`: `x` is a cut point of poly1-edge `e` (using `hfin`); of the two
  `e`-pieces adjacent to `x`, FLIP gives one whose midpoint is in `poly2.interior`, which is
  therefore kept (via `piece_kept_of_interior`) and has `x` as an endpoint, so it is an `M`-edge.
* (1) `Mlist_even_degree`: at an interior cut point `v` the two adjacent pieces straddle a single
  crossing, so FLIP makes exactly one kept (contribution `1` on each of the poly1- and poly2-edge
  through `v`, total degree `2`); at an original vertex (no crossing) `even_odd_constancy` makes
  both adjacent midpoints share interior status, giving degree `0` or `2`. All even.

The FLIP lemma itself is the genuine blocker. Proving it requires a single-crossing analogue of
`subRay_count_eq` (the crossing count across the window `[P,Q]` changes by exactly `1` at the
transversal point `c`), together with the *full* genericity/perturbation development of
`Constancy.lean` (`Rrat`, `leg1_bf`/`leg2_bf`, `exists_bad_k`) re-deployed to move `P`/`Q` a tiny
generic amount **off** the edge line `e` so the connecting ray avoids `poly`'s vertices and meets
its boundary transversally — `even_odd_constancy` certifies the perturbation preserves interior
status. This is a development of comparable size to `Constancy.lean` and is left for future work
rather than admitted with `sorry`.
-/

end Polygons2
end
