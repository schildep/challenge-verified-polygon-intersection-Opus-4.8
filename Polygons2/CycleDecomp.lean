import Mathlib
import Polygons2.PolgonIntersection2Defs
open Classical
noncomputable section
namespace Polygons2

/-! ## Basic edge / degree machinery -/

abbrev Edge := Vector2D × Vector2D

/-- `incident c e` is true when `c` is one of the endpoints of edge `e`. -/
def incident (c : Vector2D) (e : Edge) : Bool := decide (e.1 = c) || decide (e.2 = c)

/-- The endpoint of `e` other than `c` (defaults sensibly if `e.1 = c`). -/
def otherEnd (c : Vector2D) (e : Edge) : Vector2D := if e.1 = c then e.2 else e.1

/-- Directed degree: counts of edges with first endpoint `v` plus edges with second endpoint `v`. -/
def deg (R : List Edge) (v : Vector2D) : ℕ :=
  R.countP (fun e => decide (e.1 = v)) + R.countP (fun e => decide (e.2 = v))

/-- Parity invariant for a walk from `start` currently at `cur`: degree is odd exactly at
`cur` and `start` (so all-even when `cur = start`). -/
def parInv (R : List Edge) (start cur : Vector2D) : Prop :=
  ∀ v, deg R v % 2 = ((if v = cur then 1 else 0) + (if v = start then 1 else 0)) % 2

/-- All edges nondegenerate. -/
def nondeg (R : List Edge) : Prop := ∀ e ∈ R, e.1 ≠ e.2

/-- Two directed pairs match up to endpoint swap. -/
def swapMatch (p : Edge) (e : Edge) : Prop := (p = e) ∨ (p.1 = e.2 ∧ p.2 = e.1)

/-- For a polygon vertex list, the cyclic consecutive pairs (with wraparound). -/
def cyclicPairs : List Vector2D → List Edge
  | [] => []
  | v :: vs => List.zip (v :: vs) (vs ++ [v])

/-- The crossing indicator for an edge regarded as a directed segment. -/
def crossE (r : Ray) (e : Edge) : Bool := decide (rayIntersectsSegment r ⟨e.1, e.2⟩)
/-- The crossing indicator for a line segment. -/
def crossS (r : Ray) (s : LineSegment) : Bool := decide (rayIntersectsSegment r s)

/-! ## Geometry: swap invariance -/

theorem toSet_swap (a b : Vector2D) :
    (⟨a,b⟩ : LineSegment).toSet = (⟨b,a⟩ : LineSegment).toSet := by
  ext p
  constructor <;> rintro ⟨t, ht0, ht1, hx, hy⟩ <;>
    exact ⟨1 - t, by linarith, by linarith, by ring_nf; ring_nf at hx; linarith,
      by ring_nf; ring_nf at hy; linarith⟩

theorem crossE_swap (r : Ray) {p e : Edge} (h : swapMatch p e) : crossE r p = crossE r e := by
  rcases h with h | ⟨h1, h2⟩
  · rw [h]
  · unfold crossE rayIntersectsSegment
    have : (⟨p.1, p.2⟩ : LineSegment).toSet = (⟨e.1, e.2⟩ : LineSegment).toSet := by
      rw [h1, h2]; exact toSet_swap e.2 e.1
    rw [this]

/-! ## Incidence / degree lemmas -/

theorem incident_cases {c : Vector2D} {e : Edge} (h : incident c e = true) :
    e.1 = c ∨ e.2 = c := by
  unfold incident at h; simp only [Bool.or_eq_true, decide_eq_true_eq] at h; exact h

theorem deg_zero_of_find_none (R : List Edge) (c : Vector2D)
    (h : R.find? (incident c) = none) : deg R c = 0 := by
  rw [List.find?_eq_none] at h
  unfold deg
  have h1 : R.countP (fun e => decide (e.1 = c)) = 0 := by
    rw [List.countP_eq_zero]; intro e he; simp only [decide_eq_true_eq]; intro he1
    exact h e he (by unfold incident; simp [he1])
  have h2 : R.countP (fun e => decide (e.2 = c)) = 0 := by
    rw [List.countP_eq_zero]; intro e he; simp only [decide_eq_true_eq]; intro he2
    exact h e he (by unfold incident; simp [he2])
  omega

theorem countP_erase_add (R : List Edge) (e : Edge) (p : Edge → Bool) (h : e ∈ R) :
    R.countP p = (R.erase e).countP p + (if p e then 1 else 0) := by
  have hperm : R.Perm (e :: R.erase e) := List.perm_cons_erase h
  rw [List.Perm.countP_eq p hperm, List.countP_cons]

theorem deg_erase (R : List Edge) (e : Edge) (v : Vector2D) (h : e ∈ R) :
    deg R v = deg (R.erase e) v
        + (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0) := by
  unfold deg
  have c1 := countP_erase_add R e (fun e => decide (e.1 = v)) h
  have c2 := countP_erase_add R e (fun e => decide (e.2 = v)) h
  simp only [decide_eq_true_eq] at c1 c2
  rw [c1, c2]
  by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v <;> simp [h1, h2] <;> omega

theorem endpoint_indicator (cur : Vector2D) (e : Edge) (v : Vector2D)
    (hinc : incident cur e = true) :
    (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)
      = (if v = cur then (1:ℕ) else 0) + (if v = otherEnd cur e then 1 else 0) := by
  have key : ∀ a b : Vector2D, (if a = b then (1:ℕ) else 0) = (if b = a then 1 else 0) := by
    intro a b; by_cases hab : a = b <;> simp [hab, eq_comm]
  unfold otherEnd
  rw [key e.1 v, key e.2 v]
  rcases incident_cases hinc with h | h
  · rw [if_pos h, ← h]
  · by_cases he1 : e.1 = cur
    · rw [if_pos he1, ← he1]
    · rw [if_neg he1, ← h]; rw [add_comm]

theorem parInv_step (R : List Edge) (start cur : Vector2D) (e : Edge)
    (hpar : parInv R start cur) (hmem : e ∈ R) (hinc : incident cur e = true) :
    parInv (R.erase e) start (otherEnd cur e) := by
  intro v
  have hd := deg_erase R e v hmem
  have hp := hpar v
  have hind := endpoint_indicator cur e v hinc
  omega

theorem deg_pos_of_par_ne (R : List Edge) (start cur : Vector2D)
    (hpar : parInv R start cur) (hne : cur ≠ start) : 0 < deg R cur := by
  have h := hpar cur
  rw [if_pos rfl, if_neg hne] at h
  omega

theorem otherEnd_ne {cur : Vector2D} {e : Edge} (hinc : incident cur e = true)
    (hnd : e.1 ≠ e.2) : otherEnd cur e ≠ cur := by
  unfold otherEnd
  rcases incident_cases hinc with h | h
  · rw [if_pos h, ← h]; exact fun hc => hnd hc.symm
  · by_cases he1 : e.1 = cur
    · rw [if_pos he1, ← he1]; exact fun hc => hnd hc.symm
    · rw [if_neg he1]; exact he1

/-! ## The walk extraction -/

/-- Walk from `cur` back to `start`, greedily consuming edges of `R`.
Returns `(verts, removed, R')`: the vertices visited (strictly after `cur`, ending just before
the closing edge to `start`), the edges removed in walk order, and the remaining edges. -/
def walkStep (start : Vector2D) (cur : Vector2D) (R : List Edge) :
    List Vector2D × List Edge × List Edge :=
  match h : R.find? (incident cur) with
  | none => ([], [], R)
  | some e =>
    let nxt := otherEnd cur e
    let R₁ := R.erase e
    if nxt = start then ([], [e], R₁)
    else
      let res := walkStep start nxt R₁
      (nxt :: res.1, e :: res.2.1, res.2.2)
  termination_by R.length
  decreasing_by
    have hmem : e ∈ R := List.mem_of_find?_eq_some h
    rw [List.length_erase_of_mem hmem]
    have : 0 < R.length := List.length_pos_of_mem hmem
    omega

theorem walkStep_close (start cur : Vector2D) (R : List Edge) (e : Edge)
    (hsome : R.find? (incident cur) = some e) (hnxt : otherEnd cur e = start) :
    walkStep start cur R = ([], [e], R.erase e) := by
  conv_lhs => rw [walkStep]; rw [hsome]; simp only [hnxt, if_pos]

theorem walkStep_recurse (start cur : Vector2D) (R : List Edge) (e : Edge)
    (hsome : R.find? (incident cur) = some e) (hnxt : otherEnd cur e ≠ start) :
    walkStep start cur R =
      (otherEnd cur e :: (walkStep start (otherEnd cur e) (R.erase e)).1,
       e :: (walkStep start (otherEnd cur e) (R.erase e)).2.1,
       (walkStep start (otherEnd cur e) (R.erase e)).2.2) := by
  conv_lhs => rw [walkStep]; rw [hsome]; simp only [hnxt, if_neg, not_false_iff]

theorem swapMatch_endpoints {cur start : Vector2D} {e : Edge}
    (hinc : incident cur e = true) (hnxt : otherEnd cur e = start) :
    swapMatch (cur, start) e := by
  unfold swapMatch otherEnd at *
  rcases incident_cases hinc with h | h
  · rw [if_pos h] at hnxt; left; exact Prod.ext h.symm hnxt.symm
  · by_cases he1 : e.1 = cur
    · rw [if_pos he1] at hnxt; left; exact Prod.ext he1.symm hnxt.symm
    · rw [if_neg he1] at hnxt; right; exact ⟨h.symm, hnxt.symm⟩

theorem swapMatch_step {cur : Vector2D} {e : Edge} (hinc : incident cur e = true) :
    swapMatch (cur, otherEnd cur e) e := by
  unfold swapMatch otherEnd
  rcases incident_cases hinc with h | h
  · rw [if_pos h]; left; exact Prod.ext h.symm rfl
  · by_cases he1 : e.1 = cur
    · rw [if_pos he1]; left; exact Prod.ext he1.symm rfl
    · rw [if_neg he1]; right; exact ⟨h.symm, rfl⟩

/-- The walk produces a valid closed walk: its directed pairs match the removed edges up to
swap, the removed edges plus the leftovers permute `R`, and the leftovers have all-even degree. -/
theorem walkStep_spec (start : Vector2D) :
    ∀ (cur : Vector2D) (R : List Edge),
      parInv R start cur → nondeg R → 0 < deg R cur →
      (let res := walkStep start cur R
       List.Forall₂ swapMatch (List.zip (cur :: res.1) (res.1 ++ [start])) res.2.1
         ∧ R.Perm (res.2.1 ++ res.2.2)
         ∧ (∀ v, deg res.2.2 v % 2 = 0)) := by
  intro cur R
  induction cur, R using walkStep.induct start with
  | case1 cur R hnone =>
      intro _ _ hpos
      exact absurd (deg_zero_of_find_none R cur hnone) (by omega)
  | case2 cur R e hsome _ hproof =>
      intro hpar hnd _
      have hmem : e ∈ R := List.mem_of_find?_eq_some hsome
      have hinc : incident cur e = true := List.find?_some hsome
      have hnxt : otherEnd cur e = start := hproof
      simp only [walkStep_close start cur R e hsome hnxt]
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_left]
        exact List.Forall₂.cons (swapMatch_endpoints hinc hnxt) List.Forall₂.nil
      · simpa using List.perm_cons_erase hmem
      · intro v
        have hpe := parInv_step R start cur e hpar hmem hinc v
        rw [hnxt] at hpe
        rw [hpe]; omega
  | case3 cur R e hsome _ _ hproof ih =>
      intro hpar hnd _
      have hmem : e ∈ R := List.mem_of_find?_eq_some hsome
      have hinc : incident cur e = true := List.find?_some hsome
      have hnxt : otherEnd cur e ≠ start := hproof
      have hpe : parInv (R.erase e) start (otherEnd cur e) :=
        parInv_step R start cur e hpar hmem hinc
      have hnd1 : nondeg (R.erase e) := fun f hf => hnd f (List.mem_of_mem_erase hf)
      have hpos1 : 0 < deg (R.erase e) (otherEnd cur e) :=
        deg_pos_of_par_ne (R.erase e) start (otherEnd cur e) hpe hnxt
      have IH := ih hpe hnd1 hpos1
      simp only at IH ⊢
      rw [walkStep_recurse start cur R e hsome hnxt]
      obtain ⟨IH1, IH2, IH3⟩ := IH
      refine ⟨?_, ?_, IH3⟩
      · simp only [List.cons_append, List.zip_cons_cons]
        exact List.Forall₂.cons (swapMatch_step hinc) IH1
      · have hp : R.Perm (e :: R.erase e) := List.perm_cons_erase hmem
        refine hp.trans ?_
        simp only [List.cons_append]
        exact IH2.cons e

theorem walkStep_top_nonempty (start : Vector2D) (R : List Edge) (e : Edge)
    (hsome : R.find? (incident start) = some e) (hnd : e.1 ≠ e.2) :
    (walkStep start start R).1 ≠ [] := by
  have hinc : incident start e = true := List.find?_some hsome
  have hne : otherEnd start e ≠ start := otherEnd_ne hinc hnd
  rw [walkStep_recurse start start R e hsome hne]
  exact List.cons_ne_nil _ _

/-! ## From a matched pair-list to polygon facts -/

theorem countP_forall2_swapMatch (r : Ray) {pairs removed : List Edge}
    (h : List.Forall₂ swapMatch pairs removed) :
    pairs.countP (crossE r) = removed.countP (crossE r) := by
  induction h with
  | nil => rfl
  | cons hpe _ ih =>
      rw [List.countP_cons, List.countP_cons, ih, crossE_swap r hpe]

theorem forall2_swapMatch_distinct {pairs removed : List Edge}
    (h : List.Forall₂ swapMatch pairs removed) (hnd : nondeg removed) :
    ∀ p ∈ pairs, p.1 ≠ p.2 := by
  induction h with
  | nil => intro p hp; simp at hp
  | @cons p e ps es hpe _ ih =>
      intro q hq
      rcases List.mem_cons.1 hq with hq | hq
      · subst hq
        have hee : e.1 ≠ e.2 := hnd e (List.mem_cons_self)
        rcases hpe with h | ⟨h1, h2⟩
        · rw [h]; exact hee
        · rw [h1, h2]; exact fun hc => hee hc.symm
      · exact ih (fun f hf => hnd f (List.mem_cons_of_mem _ hf)) q hq

/-- A `swapMatch` upgrades to equality of segment point sets. -/
theorem toSet_of_swapMatch {p e : Edge} (h : swapMatch p e) :
    (⟨p.1, p.2⟩ : LineSegment).toSet = (⟨e.1, e.2⟩ : LineSegment).toSet := by
  rcases h with h | ⟨h1, h2⟩
  · rw [h]
  · rw [h1, h2]; exact toSet_swap e.2 e.1

/-- A `swapMatch` makes both endpoints of `p` endpoints of `e`. -/
theorem endpoints_of_swapMatch {p e : Edge} (h : swapMatch p e) :
    (p.1 = e.1 ∨ p.1 = e.2) ∧ (p.2 = e.1 ∨ p.2 = e.2) := by
  rcases h with h | ⟨h1, h2⟩
  · rw [h]; exact ⟨Or.inl rfl, Or.inr rfl⟩
  · exact ⟨Or.inr h1, Or.inl h2⟩

/-- Each matched pair's segment equals some removed edge's segment as a point set. -/
theorem forall2_swapMatch_seg {pairs removed : List Edge}
    (h : List.Forall₂ swapMatch pairs removed) :
    ∀ p ∈ pairs, ∃ e ∈ removed, (⟨p.1, p.2⟩ : LineSegment).toSet = (⟨e.1, e.2⟩ : LineSegment).toSet := by
  induction h with
  | nil => intro p hp; simp at hp
  | @cons p e ps es hpe _ ih =>
      intro q hq
      rcases List.mem_cons.1 hq with hq | hq
      · subst hq
        exact ⟨e, List.mem_cons_self, toSet_of_swapMatch hpe⟩
      · obtain ⟨f, hf, hfs⟩ := ih q hq
        exact ⟨f, List.mem_cons_of_mem _ hf, hfs⟩

/-- Each removed edge's segment equals some matched pair's segment as a point set (reverse). -/
theorem forall2_swapMatch_seg_rev {pairs removed : List Edge}
    (h : List.Forall₂ swapMatch pairs removed) :
    ∀ e ∈ removed, ∃ p ∈ pairs, (⟨e.1, e.2⟩ : LineSegment).toSet = (⟨p.1, p.2⟩ : LineSegment).toSet := by
  induction h with
  | nil => intro e he; simp at he
  | @cons p e ps es hpe _ ih =>
      intro f hf
      rcases List.mem_cons.1 hf with hf | hf
      · subst hf
        exact ⟨p, List.mem_cons_self, (toSet_of_swapMatch hpe).symm⟩
      · obtain ⟨q, hq, hqs⟩ := ih f hf
        exact ⟨q, List.mem_cons_of_mem _ hq, hqs⟩

/-- Each matched pair's first endpoint is an endpoint of some removed edge. -/
theorem forall2_swapMatch_fst {pairs removed : List Edge}
    (h : List.Forall₂ swapMatch pairs removed) :
    ∀ p ∈ pairs, ∃ e ∈ removed, p.1 = e.1 ∨ p.1 = e.2 := by
  induction h with
  | nil => intro p hp; simp at hp
  | @cons p e ps es hpe _ ih =>
      intro q hq
      rcases List.mem_cons.1 hq with hq | hq
      · subst hq
        exact ⟨e, List.mem_cons_self, (endpoints_of_swapMatch hpe).1⟩
      · obtain ⟨f, hf, hfs⟩ := ih q hq
        exact ⟨f, List.mem_cons_of_mem _ hf, hfs⟩

/-- When the second list is at least as long, every element of the first list is the first
component of some pair in the zip. -/
theorem mem_fst_zip {α β : Type*} (l₁ : List α) (l₂ : List β) (hlen : l₁.length ≤ l₂.length) :
    ∀ a ∈ l₁, ∃ q ∈ List.zip l₁ l₂, q.1 = a := by
  induction l₁ generalizing l₂ with
  | nil => intro a ha; simp at ha
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons y ys =>
          intro a ha
          rcases List.mem_cons.1 ha with ha | ha
          · subst ha; exact ⟨(a, y), by simp [List.zip_cons_cons], rfl⟩
          · have hlen' : xs.length ≤ ys.length := by
              simp only [List.length_cons] at hlen; omega
            obtain ⟨q, hq, hq1⟩ := ih ys hlen' a ha
            exact ⟨q, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq, hq1⟩

/-- Segments of `Polygon.mk (v :: vs)` realized via `cyclicPairs`. -/
theorem segments_eq_cyclicPairs (v : Vector2D) (vs : List Vector2D) (hvs : vs ≠ []) :
    (Polygon.mk (v :: vs)).segments
      = (cyclicPairs (v :: vs)).map (fun p => ⟨p.1, p.2⟩) := by
  unfold Polygon.segments cyclicPairs
  cases vs with
  | nil => exact absurd rfl hvs
  | cons w ws => rfl

theorem segments_countP (r : Ray) (v : Vector2D) (vs : List Vector2D) (hvs : vs ≠ []) :
    (Polygon.mk (v :: vs)).segments.countP (crossS r)
      = (cyclicPairs (v :: vs)).countP (crossE r) := by
  rw [segments_eq_cyclicPairs v vs hvs, List.countP_map]
  rfl

/-! ## Packaging one extracted cycle -/

/-- The result of extracting one closed walk starting at `start` from `R`. -/
structure CycleResult (R : List Edge) where
  poly : Polygon
  rest : List Edge
  walkPairs : List Edge
  hperm : R.Perm (walkPairs ++ rest)
  hcross : ∀ r : Ray, poly.segments.countP (crossS r) = walkPairs.countP (crossE r)
  hnd : ∀ s ∈ poly.segments, s.p1 ≠ s.p2
  hseg_edge : ∀ s ∈ poly.segments, ∃ e ∈ walkPairs, s.toSet = (LineSegment.mk e.1 e.2).toSet
  hcover : ∀ e ∈ walkPairs, ∃ s ∈ poly.segments, s.toSet = (LineSegment.mk e.1 e.2).toSet
  hvert_end : ∀ v ∈ poly.vertices, ∃ e ∈ walkPairs, v = e.1 ∨ v = e.2
  hrest_even : ∀ v, deg rest v % 2 = 0
  hrest_lt : rest.length < R.length

def extract_cycle (R : List Edge) (start : Vector2D)
    (hpar : parInv R start start) (hnd : nondeg R) (hpos : 0 < deg R start) :
    CycleResult R := by
  rcases hfind : R.find? (incident start) with _ | e'
  · exact absurd (deg_zero_of_find_none R start hfind) (by omega)
  · -- the extracted walk
    set res := walkStep start start R with hres
    have hnde' : e'.1 ≠ e'.2 := hnd e' (List.mem_of_find?_eq_some hfind)
    have hverts_ne : res.1 ≠ [] := by
      rw [hres]; exact walkStep_top_nonempty start R e' hfind hnde'
    have hspec := walkStep_spec start start R hpar hnd hpos
    simp only [← hres] at hspec
    obtain ⟨hF, hP, hE⟩ := hspec
    refine
      { poly := Polygon.mk (start :: res.1)
        rest := res.2.2
        walkPairs := res.2.1
        hperm := hP
        hcross := ?_
        hnd := ?_
        hseg_edge := ?_
        hcover := ?_
        hvert_end := ?_
        hrest_even := hE
        hrest_lt := ?_ }
    · intro r
      have hcp : cyclicPairs (start :: res.1) = List.zip (start :: res.1) (res.1 ++ [start]) := rfl
      rw [segments_countP r start res.1 hverts_ne, hcp]
      exact countP_forall2_swapMatch r hF
    · -- nondegeneracy of segments
      intro s hs
      rw [segments_eq_cyclicPairs start res.1 hverts_ne] at hs
      simp only [List.mem_map] at hs
      obtain ⟨p, hp, hps⟩ := hs
      have hcp : cyclicPairs (start :: res.1) = List.zip (start :: res.1) (res.1 ++ [start]) := rfl
      rw [hcp] at hp
      have hdist := forall2_swapMatch_distinct hF (fun f hf => hnd f ?_) p hp
      · rw [← hps]; exact hdist
      · have := hP.mem_iff (a := f)
        exact this.2 (List.mem_append_left _ hf)
    · -- each segment equals some walkPairs edge as a point set
      intro s hs
      rw [segments_eq_cyclicPairs start res.1 hverts_ne] at hs
      simp only [List.mem_map] at hs
      obtain ⟨p, hp, hps⟩ := hs
      have hcp : cyclicPairs (start :: res.1) = List.zip (start :: res.1) (res.1 ++ [start]) := rfl
      rw [hcp] at hp
      obtain ⟨e, he, hes⟩ := forall2_swapMatch_seg hF p hp
      exact ⟨e, he, by rw [← hps]; exact hes⟩
    · -- each walkPairs edge is realized as some segment
      intro e he
      obtain ⟨p, hp, hps⟩ := forall2_swapMatch_seg_rev hF e he
      refine ⟨⟨p.1, p.2⟩, ?_, hps.symm⟩
      rw [segments_eq_cyclicPairs start res.1 hverts_ne]
      simp only [List.mem_map]
      have hcp : cyclicPairs (start :: res.1) = List.zip (start :: res.1) (res.1 ++ [start]) := rfl
      exact ⟨p, by rw [hcp]; exact hp, rfl⟩
    · -- each vertex is an endpoint of some walkPairs edge
      intro v hv
      -- vertices of poly = start :: res.1; each is a first component of a cyclic pair
      have hvmem : v ∈ start :: res.1 := hv
      have hlen : (start :: res.1).length ≤ (res.1 ++ [start]).length := by
        simp [List.length_append]
      obtain ⟨q, hq, hq1⟩ := mem_fst_zip (start :: res.1) (res.1 ++ [start]) hlen v hvmem
      obtain ⟨e, he, hee⟩ := forall2_swapMatch_fst hF q hq
      rw [hq1] at hee
      exact ⟨e, he, hee⟩
    · -- rest.length < R.length
      have hlen : R.length = res.2.1.length + res.2.2.length := by
        have := hP.length_eq; simpa using this
      have hpos1 : 0 < res.2.1.length := by
        have hFlen := hF.length_eq
        rw [List.length_zip] at hFlen
        simp only [List.length_cons, List.length_append] at hFlen
        omega
      omega

/-! ## The decomposition recursion -/

theorem decomp (M : List Edge)
    (hnd : nondeg M) (hdeg : ∀ v, deg M v % 2 = 0) :
    ∃ polys : List Polygon,
      (∀ Q ∈ polys, ∀ s ∈ Q.segments, s.p1 ≠ s.p2) ∧
      (∀ r : Ray,
        (polys.map (fun Q => Q.segments)).flatten.countP (crossS r)
          = M.countP (crossE r)) ∧
      (∀ Q ∈ polys, ∀ s ∈ Q.segments,
          ∃ e ∈ M, s.toSet = (LineSegment.mk e.1 e.2).toSet) ∧
      (∀ Q ∈ polys, ∀ v ∈ Q.vertices,
          ∃ e ∈ M, v = e.1 ∨ v = e.2) ∧
      (∀ e ∈ M, ∃ Q ∈ polys, ∃ s ∈ Q.segments,
          s.toSet = (LineSegment.mk e.1 e.2).toSet) := by
  induction hlen : M.length using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    subst hlen
    rcases hM : M with _ | ⟨e0, M0⟩
    · -- empty
      refine ⟨[], ?_, ?_, ?_, ?_, ?_⟩
      · intro Q hQ; simp at hQ
      · intro r; simp
      · intro Q hQ; simp at hQ
      · intro Q hQ; simp at hQ
      · intro e he; simp at he
    · -- nonempty: extract a cycle from start = e0.1
      set start := e0.1 with hstart
      have hpar : parInv M start start := by
        intro v
        rw [hdeg v]
        by_cases hv : v = start <;> simp [hv]
      have hpos : 0 < deg M start := by
        -- e0 ∈ M with e0.1 = start contributes to deg
        have he0 : e0 ∈ M := by rw [hM]; exact List.mem_cons_self
        have hmf : e0 ∈ M.filter (fun e => decide (e.1 = start)) :=
          List.mem_filter.2 ⟨he0, by simp [hstart]⟩
        have : 0 < M.countP (fun e => decide (e.1 = start)) := by
          rw [List.countP_eq_length_filter]; exact List.length_pos_of_mem hmf
        unfold deg; omega
      have cr := extract_cycle M start hpar hnd hpos
      -- recurse on cr.rest
      have hnd_rest : nondeg cr.rest := by
        intro f hf
        exact hnd f ((cr.hperm.mem_iff).2 (List.mem_append_right _ hf))
      have IH := ih cr.rest.length cr.hrest_lt cr.rest hnd_rest cr.hrest_even rfl
      obtain ⟨polys', hpolys_nd, hpolys_cross, hpolys_seg, hpolys_vert, hpolys_cover⟩ := IH
      -- membership in walkPairs implies membership in M (= e0 :: M0)
      have hwp_mem : ∀ e ∈ cr.walkPairs, e ∈ M := fun e he =>
        (cr.hperm.mem_iff).2 (List.mem_append_left _ he)
      have hrest_mem : ∀ e ∈ cr.rest, e ∈ M := fun e he =>
        (cr.hperm.mem_iff).2 (List.mem_append_right _ he)
      refine ⟨cr.poly :: polys', ?_, ?_, ?_, ?_, ?_⟩
      · intro Q hQ s hs
        rcases List.mem_cons.1 hQ with hQ | hQ
        · subst hQ; exact cr.hnd s hs
        · exact hpolys_nd Q hQ s hs
      · intro r
        simp only [List.map_cons, List.flatten_cons, List.countP_append]
        rw [cr.hcross r, hpolys_cross r, ← hM]
        rw [cr.hperm.countP_eq (crossE r), List.countP_append]
      · intro Q hQ s hs
        rcases List.mem_cons.1 hQ with hQ | hQ
        · subst hQ
          obtain ⟨e, he, hes⟩ := cr.hseg_edge s hs
          exact ⟨e, hM ▸ hwp_mem e he, hes⟩
        · obtain ⟨e, he, hes⟩ := hpolys_seg Q hQ s hs
          exact ⟨e, hM ▸ hrest_mem e he, hes⟩
      · intro Q hQ v hv
        rcases List.mem_cons.1 hQ with hQ | hQ
        · subst hQ
          obtain ⟨e, he, hee⟩ := cr.hvert_end v hv
          exact ⟨e, hM ▸ hwp_mem e he, hee⟩
        · obtain ⟨e, he, hee⟩ := hpolys_vert Q hQ v hv
          exact ⟨e, hM ▸ hrest_mem e he, hee⟩
      · intro e he
        have hmem : e ∈ cr.walkPairs ++ cr.rest := (cr.hperm.mem_iff).1 (hM ▸ he)
        rcases List.mem_append.1 hmem with hw | hr
        · obtain ⟨s, hs, hse⟩ := cr.hcover e hw
          exact ⟨cr.poly, List.mem_cons_self, s, hs, hse⟩
        · obtain ⟨Q, hQ, s, hs, hse⟩ := hpolys_cover e hr
          exact ⟨Q, List.mem_cons_of_mem _ hQ, s, hs, hse⟩

/-! ## The main theorem -/

theorem cycle_decomp (M : List (Vector2D × Vector2D))
    (hnd : ∀ e ∈ M, e.1 ≠ e.2)
    (hdeg : ∀ v : Vector2D,
        (M.countP (fun e => decide (e.1 = v)) + M.countP (fun e => decide (e.2 = v))) % 2 = 0) :
    ∃ polys : List Polygon,
      (∀ Q ∈ polys, ∀ s ∈ Q.segments, s.p1 ≠ s.p2) ∧
      (∀ r : Ray,
        (polys.map (fun Q => Q.segments)).flatten.countP
            (fun s => decide (rayIntersectsSegment r s))
          = M.countP (fun e => decide (rayIntersectsSegment r ⟨e.1, e.2⟩))) ∧
      (∀ Q ∈ polys, ∀ s ∈ Q.segments,
          ∃ e ∈ M, s.toSet = (LineSegment.mk e.1 e.2).toSet) ∧
      (∀ Q ∈ polys, ∀ v ∈ Q.vertices,
          ∃ e ∈ M, v = e.1 ∨ v = e.2) ∧
      (∀ e ∈ M, ∃ Q ∈ polys, ∃ s ∈ Q.segments,
          s.toSet = (LineSegment.mk e.1 e.2).toSet) := by
  have := decomp M hnd hdeg
  obtain ⟨polys, h1, h2, h3, h4, h5⟩ := this
  exact ⟨polys, h1, h2, h3, h4, h5⟩

end Polygons2
end
