# Informal Proof: Polygon Intersection

> **STATUS: COMPLETE.**  The spec theorem
> `exists_polygons_inter_interior_eq_symmDiffAll_interiors_sdiff_boundaries`
> (in the read-only `PolgonIntersection2.lean`) is fully proven, with **no `sorry`/`axiom`/`admit`**.
> `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` (standard Mathlib axioms).
> The whole project builds (`lake build`, exit 0).  Honest construction: the output polygons are
> the genuine clipped intersection-boundary cycles, with no input-edge duplication.
>
> Proof spine (file → role): `Geom`/`Cross`/`CrossSigns`/`SectorCore`/`Telescope`/`Independence`
> → `RayIndep` (ray-independence of even–odd crossing parity); `Interior`/`Bridge`/`SubRay`/
> `RayParam`/`PairCount`/`CrossSeq` → interior characterisation + `symmDiffAll` bridge;
> `Clip`/`ClipM`/`ClipProps` → clipped boundary `Mlist` (nondeg, ⊆∂A∪∂B, `countP = insideCrossings`,
> `mem_of_inside`); `Constancy` → `even_odd_constancy` (local constancy across boundary-free
> segments — the deep crux); `EvenDegA` → `Mlist_even_degree` (converse-of-ray-independence);
> `CycleDecomp` → realise `Mlist` as polygon cycles (with edge coverage); `AcapBA`+`CornerC` →
> `AcapB_const` (A∩B constant off `Mlist`, via the corner lemma `endpoint_off_double_C`);
> `Assemble`/`Assemble2`/`Assemble3` → `intersection_polys_core` (anchor+transfer, no `hSsub`);
> `Construction` → `exists_intersection_polys`; `PolgonIntersection2Proof` → main theorem.


Goal: given `poly1`, `poly2` (len ≥ 2, nondegenerate segments, finite boundary
intersection `h_fin`), exhibit `polys : List Polygon` with
```
A ∩ B = symmDiffAll (polys.map interior) \ { p | ∃ q ∈ polys, p ∈ q.toBoundarySet }
```
where `A := poly1.interior`, `B := poly2.interior`.

## Settled facts (verified by analysis + adversarial review)

* `interior` = even–odd ("crossing parity") interior; condition 1 excludes the
  polygon's own boundary; condition 2 requires odd crossing parity for **every**
  vertex-avoiding ray.
* `intersectionRayPolygonSegmentsNumber r poly = poly.segments.countP (rayIntersectsSegment r ·)`
  is **additive over segment-list concatenation** (`List.countP_append`); crossing
  parity is XOR under multiset-union of edges.  Order of edges is irrelevant.
* A **doubled** segment (same `toSet`, e.g. `(a,b)` & `(b,a)`) contributes 0 mod 2.
* `toBoundarySet` is always ≤ 1-D (each `seg.toSet` is the affine image of `[0,1]`).
  So `\ boundary` can only repair a ≤1-D discrepancy.
* **Obstruction:** off all edge-lines, `symmDiffAll(interiors)` is the pointwise XOR
  of the `1_{interior Pᵢ}`.  `1_A·1_B` (AND) is non-affine over GF(2), so it cannot
  be an XOR of `A,B` and empty-interior polygons.  We **must** realize a genuinely
  clipped region as an even–odd polygon.
* **Decompositions are WRONG.**  Any partition of `A∩B` into ≥2 pieces whose shared
  internal edges lie inside `A∩B` deletes those seam points: a seam point is in the
  target `A∩B` but lies on two pieces' boundaries (in neither piece's interior, and
  removed by `\ boundary`).  Concretely splitting `(2,4)²` at `x=3` loses `(3,3)`.
  ⇒ triangulation / line-arrangement-cells / trapezoids all fail.

## The construction: the intersection-boundary polygon(s)

Let `S := ∂A ∩ ∂B` (= `poly1.toBoundarySet ∩ poly2.toBoundarySet`), finite by
`h_fin`.  `h_fin` ⇔ no edge of poly1 is collinear-overlapping an edge of poly2.

Define the **edge multiset** `M`:
* for each edge `e` of poly1: the maximal sub-segments of `e` cut at points of `S`
  that lie **inside `B`** (π₂ = 1 on them);
* for each edge `f` of poly2: the maximal sub-segments of `f` cut at `S`
  that lie **inside `A`** (π₁ = 1 on them).

`M` is exactly the edge set of `∂(A∩B)`.  Every edge of `M` is a sub-segment of a
poly1/poly2 edge, so the union of `M`-edge point-sets is `⊆ ∂A ∪ ∂B`, which `A∩B`
avoids.

`M` has **even degree** at every point (boundary of a region is a mod-2 1-cycle):
decompose `M` into closed walks (cycles) and realize each walk as a `Polygon`
(vertex list `v₀,…,v_k` ⇒ segments `(v₀,v₁),…,(v_k,v₀)`).  `polys` = these polygons.

## Why it works

Write `π_Q(p)` = crossing parity of polygon/edge-multiset `Q` at `p` (off `Q`'s
edges).  The proof rests on three pillars.

### Pillar 1 — Ray-independence (the core lemma).  No topology needed.
For a closed edge multiset `Q` (every vertex even degree — automatic for a single
vertex cycle, degree 2) and `p` off all edges: `intersectionRay… r poly % 2` is the
**same** for all vertex-avoiding rays `r` from `p`.  Hence `π_Q(p)` is well-defined
and `interior_Q ∩ {off edges} = {p : π_Q(p)=1}`.

*Proof.*  Compare two vertex-avoiding rays `r₁,r₂` from `p` (directions `d₁,d₂`).
Let `status(v)` = "`v−p` lies in the open angular sector bounded by `d₁,d₂`"
(well-defined: no vertex on `r₁`/`r₂` since rays avoid vertices).  Walk the cycle
`v₀→v₁→…→v₀`; `Σᵢ (status(vᵢ)⊕status(vᵢ₊₁)) = 0` (telescopes around the closed
cycle).  Per edge `eᵢ=(vᵢ,vᵢ₊₁)`: `status(vᵢ)⊕status(vᵢ₊₁) = cross(r₁,eᵢ)⊕cross(r₂,eᵢ)`
(a finite geometric fact: a segment meets a vertex-avoiding ray in ≤1 point —
collinear-overlap is impossible because it would force the ray through an endpoint
= a vertex; crossing a sector-boundary ray toggles in-sector status).  Summing:
`N(r₁) ⊕ N(r₂) = Σ (cross(r₁,eᵢ)⊕cross(r₂,eᵢ)) = 0`.  ∎

### Pillar 2 — Parity additivity.
For a transversal ray `r` (avoids all vertices, crosses no edge tangentially) and an
edge multiset that is a disjoint union, `π = ⊕ countP` via `List.countP_append`.
In particular `π_{poly1}=1_A`, `π_{poly2}=1_B` off edges, and `π_M = ⊕` of the
cycle parities (so `symmDiffAll(map interior polys) ∩ {off edges} = {π_M = 1}`).

### Pillar 3 — 1-D flip counting: `π_M(p) = 1_{A∩B}(p)`.
Fix `p` off all edges; choose (by ray-independence, any) a **transversal** ray `r`
from `p` avoiding `S`, all vertices, missing tangencies.  March `q` along `r` from
`p` to `∞`.  `π₁(q)` flips exactly at poly1-edge crossings, `π₂(q)` at poly2-edge
crossings.  An `M`-edge is crossed ⇔ the **`A∩B`-status `π₁∧π₂` flips** (a poly1
piece is in `M` iff inside `B`, i.e. `π₂=1` there; crossing it flips `π₁∧π₂`).
Far out, `π₁=π₂=0`.  So `N_M(r) ≡ #flips ≡ (π₁∧π₂)(p) = 1_{A∩B}(p)` (mod 2).

### Assembly of the final equation
For `p` on some `polys`-boundary (⊆ `∂A∪∂B`): excluded from RHS and (being on
`∂A`/`∂B`) not in `A∩B` — both sides exclude.  For `p` off all boundaries:
`p ∈ RHS ⇔ π_M(p)=1 ⇔ p∈A∩B` (Pillars 2,3).  Done.

## CURRENT STATE (verified vs. remaining)

The whole project **builds**; the *only* `sorry` is in `Construction.lean`'s
`exists_intersection_polys`.  Everything below it is machine-checked, axiom-free:

* `RayIndep.ray_indep` — ray-independence of even–odd crossing parity (the deep core).
* `Interior.mem_interior_iff` — interior membership via any single vertex-avoiding ray.
* `Interior.mem_symmDiffAll` — XOR membership of `symmDiffAll`.
* `Bridge.symmDiffAll_interior_iff` — `p ∈ symmDiffAll(interiors)` ⇔ crossing parity of the
  concatenated edge list (for `p` off all edges, common good ray).
* `PolgonIntersection2Proof` — the **main theorem assembly**: given
  `exists_intersection_polys`, derives the goal via the bridge + boundary case split.

So the theorem is reduced, fully verified, to one geometric construction lemma:

> `exists_intersection_polys`: there is a list `polys` of (nondegenerate) polygons whose
> boundaries lie in `∂poly1 ∪ ∂poly2`, and such that for every `p` off those boundaries
> there is a vertex-avoiding ray whose combined-edge crossing parity is `1` iff
> `p ∈ poly1.interior ∩ poly2.interior`.

### DETAILED PLAN for `exists_intersection_polys` (the construction)

Write `A = poly1.interior`, `B = poly2.interior`, `N₁(r)/N₂(r)` = #crossings of ray `r`
with poly1/poly2.  The construction realizes the clipped boundary `M = ∂(A∩B)`:
`M = {poly1-edge sub-pieces inside B} ∪ {poly2-edge sub-pieces inside A}`.

**Pillar (1-D flip) — REFINED: no sorting needed, pure pairs-counting.**
For a generic ray `r` from `p` (avoids all vertices and all of `S`, so it meets each edge
in ≤1 transversal point and all crossing points are distinct):
* `M.countP(crossB r) = #(poly1 edges crossed at a point ∈ B) + #(poly2 edges crossed at a
  point ∈ A)` — because `r` meets edge `e` at one point `q_e`, lying in exactly one clip-piece
  of `e`, which is kept in `M` iff `q_e` is inside the other polygon.
* `[q₁ ∈ B] ≡ #(poly2-crossings of r strictly beyond q₁)  (mod 2)` — `mem_interior_iff` on the
  sub-ray of `r` from `q₁`.  So `#(poly1 crossed inside B) ≡ Σ_{q₁}#{poly2-crossings beyond q₁}`.
* `Σ_{q₁}#{q₂ beyond q₁} + Σ_{q₂}#{q₁ beyond q₂} = N₁·N₂`: every (poly1-crossing, poly2-crossing)
  pair has exactly one of the two "beyond" the other (distinct distances), so the two sums
  count complementary halves of all `N₁·N₂` pairs.  ⇒ `M.countP(crossB r) ≡ N₁·N₂`.
* `N₁·N₂ ≡ (parity N₁)(parity N₂) = 1_A(p)·1_B(p) = 1_{A∩B}(p)` by `mem_interior_iff` at `p`.

**Even degree of `M` (needed for C2).**  At an intersection point `s` (poly1 `e₁` meets poly2
`e₂`): crossing `e₂` flips inside-`B`, so exactly one of the two `e₁`-pieces at `s` is kept,
and likewise one `e₂`-piece ⇒ degree 2.  At an original vertex `v`: both incident pieces share
`v`'s inside-status ⇒ degree 0 or 2.  Either way even.

(Original cseq formulation kept in `CrossSeq.lean`; the pairs-counting route above is the one
used for `C5`.)

**Pillar (1-D flip), the original combinatorial identity (in `CrossSeq.lean`).**
For a *generic* ray `r` from `p` (avoids all arrangement vertices, not parallel to any
edge, misses all of `S`), order its crossings with poly1/poly2 edges by distance into a
`List Bool` (`true` = poly1-crossing, `false` = poly2-crossing).  Then:
* `N_M(r) = #(poly1-crossings whose point ∈ B) + #(poly2-crossings whose point ∈ A)`
  — because each M-piece is crossed iff the corresponding edge is crossed at an
  inside-point.
* `point q₁ of a poly1-crossing ∈ B  ⇔  odd #(poly2-crossings beyond q₁)` — this is
  `mem_interior_iff` applied to **poly2** and the sub-ray of `r` starting at `q₁` (already
  proven!).  Likewise for poly2-crossings and `A`.
* **Combinatorial identity** (pure `List Bool`):
  `#{i : l i = true ∧ Odd #{j>i: l j = false}} + #{j : l j = false ∧ Odd #{i>j: l i = true}}
     ≡ (#true)·(#false)  (mod 2)`.
  Proof: first term `≡ #(true-before-false pairs)`, second `≡ #(false-before-true pairs)`;
  their sum `= (#true)(#false)`.
* `(#true)(#false) = N₁(r)·N₂(r) ≡ (parity N₁)(parity N₂) = 1_A(p)·1_B(p) = 1_{A∩B}(p)`
  by `mem_interior_iff` for poly1, poly2 at `p` with ray `r`.

So `N_M(r) ≡ 1_{A∩B}(p)`; with `ray_indep` this transfers to *every* good ray.

**Pillar (cycle realization).**  `M` has even degree at every node (boundary of a region),
so it decomposes into closed walks; realize each as a `Polygon`.  Combined segments `= M`
⇒ combined crossing parity `= π_M`.  `Bd = M`-points `⊆ ∂A ∪ ∂B`.

**Pillar (clipping).** Build `M`: per edge, split at the finite `S`-points on it
(sorted by parameter), keep pieces whose midpoint is inside the other interior.  Prove
even degree and `⊆ ∂A∪∂B`.

### CORRECTION (no input doubling — honest algorithm)
An earlier idea augmented `M` with the doubled full input edges to force `Bd = ∂A∪∂B`.
**Rejected**: the eventual goal is to extract an *algorithm* from the theorem, and that algorithm
must not systematically duplicate input segments.  So `polys =` the genuine clipped
intersection-boundary cycles only (`cycle_decomp Mcore`), and points on `∂A`/`∂B` but off
`∂(A∩B)` are handled honestly via the local-constancy lemma below.

### THE CRUX LEMMA (`even_odd_constancy` / 2-origin flip)
> For a polygon `poly` (nondegenerate segments) and points `P, Q` with the closed segment
> `[P,Q]` disjoint from `poly.toBoundarySet`:  `P ∈ poly.interior ↔ Q ∈ poly.interior`.

This is local constancy of the even-odd interior across boundary-free segments.  The clip's
`Mlist_even_degree` and `Mlist_countP_eq_insideCrossings`, and the assembly's handling of points
on `∂A∪∂B`, all reduce to it.  Proof plan:
* `flip_subRay` (proved in `ClipM`): if a ray `rr` avoids `poly`'s vertices and no point of `rr`
  with parameter in `[t₁,t₂]` lies on `∂poly`, the two sub-ray origins have equal interior status.
  This is the **same-ray** special case.
* General case via a **2-hop** `P → R → Q`: choose `R` slightly off the line `PQ` so that the
  rays `P→R` and `R→Q` avoid `poly`'s vertices (generic rational direction) and `[P,R]`, `[R,Q]`
  stay in the boundary-free open neighbourhood of `[P,Q]` (a point/segment off finitely many
  closed segments has a positive rational separation).  Apply `flip_subRay` on each hop.

### KEY SIMPLIFICATION (SUPERSEDED): augment M with doubled full edges
Define `M = Mcore ++ doubled(poly1.segments ++ poly2.segments)` where `Mcore` = the clipped
inside-pieces (the real `∂(A∩B)` edges), and the doubled full polygon edges appear twice.
* Doubled edges contribute `0` to crossing parity ⇒ `M.countP(crossB r) ≡ Mcore.countP = insideCrossings (mod 2)`.
* Doubled list ⇒ every vertex has even degree from that part; with `Mcore` even-degree, `M` is even-degree.
* `M`'s edge point-set now **contains all of `∂A ∪ ∂B`** (the full edges), and is `⊆ ∂A∪∂B`.
  So after cycle realization, `Bd = ∂A ∪ ∂B` exactly.
* Therefore in C6, "p ∉ Bd" ⇔ "p off `∂A` and off `∂B`" — a clean point, so `mem_interior_iff`
  applies to both polygons with a ray that avoids all original vertices and `S`. **This removes
  the polygon-vertex / on-boundary edge cases entirely.**
So C4 only needs `Mcore` (clipping); the doubling is handled trivially in C6.

### C6 assembly: anchor + transfer (clean, no input doubling)
`polys = cycle_decomp Mcore` (the honest intersection cycles).  For the parity condition at a
point `p` off `Bd` (= off `Mcore`-edges = off `∂(A∩B)`):
* **Anchor** (for `p'` off `∂A ∪ ∂B`): `[p' ∈ symmDiffAll(polys)] ↔ [p' ∈ A∩B]` — via the bridge
  (`r'` from `p'` avoiding `polys`' vertices), `cycle_decomp` (`combined = Mcore.countP`),
  `Mlist_countP_eq_insideCrossings`, `insideCrossings_parity` (C5), and `mem_interior_iff`.  All
  clean because `p'` is off both boundaries.
* **Transfer** to any `p` off `Mcore`-edges: pick `p'` off `∂A∪∂B` near `p` with `[p,p']` off
  `Mcore`-edges; `even_odd_constancy` (per `polys` cycle) gives `[p∈symmDiffAll]=[p'∈symmDiffAll]`.
  - `p` off `∂A∪∂B` (case a): take `p'=p`, anchor directly.
  - `p` on `∂A` (case b): `p` is outside `B` (`Mlist_mem_of_inside` contrapositive), so a nearby
    `p'` is outside `B` ⇒ `[p'∈A∩B]=0=[p∈A∩B]`; combine with anchor + transfer.  Symmetric on `∂B`.
  - `p∈S` is excluded: every `S`-point lies on an `Mcore`-edge.
* Final `r` from `p` avoids `polys`' vertices (⊆ vertices, which lie on `polys` segments via
  `vertex_on_boundary`, so `p∉` them by `hpoff`); bridge gives `combined%2=1 ↔ [p∈symmDiffAll] ↔ [p∈A∩B]`.

### Remaining pieces (all reduce to even_odd_constancy)
* `even_odd_constancy` (delegated) + a reusable "nearby point off finite segments" (openness) helper.
* `Mlist_even_degree`, `Mlist_countP_eq_insideCrossings` (ClipM) — via `even_odd_constancy`.
* `Mlist_mem_of_inside` (`p∈∂A` ∧ `p∈B` ⇒ `p∈Mcore`-edge) and `S ⊆ Mcore`-edges (ClipM).
* C6 anchor + transfer.

### Sub-lemmas / build order for the construction
C1. (pure) Combinatorial identity above on `List Bool`.
C2. (pure) Cycle decomposition: even-degree edge list ⇒ `List Polygon` with matching
    crossing counts.
C3. Generic ray existence (extend `exists_good_dir`: avoid vertices, edge-directions, `S`).
C4. Clip: define `M`; even degree; `M`-edges ⊆ `∂A∪∂B`; nondegenerate.
C5. Geometric glue: order `r`'s crossings; `N_M(r)` = inside-crossing counts; inside ⇔
    odd-beyond (via `mem_interior_iff`); combine with C1 ⇒ `N_M(r) ≡ 1_{A∩B}(p)`.
C6. Assemble `exists_intersection_polys` from C2–C5 + bridge-compatible parities.

### Remaining work (the clipping construction)
`polys` must realize the edge multiset `M = ∂(A∩B)` (poly1-arcs inside `B`, poly2-arcs
inside `A`) as polygon cycles.  Sub-pieces:
1. Clip each edge at `S = ∂A∩∂B` (finite by `h_fin`); inside/outside (`π_other`) constant
   per piece; collect `M`.  Prove `M`-edges ⊆ `∂A ∪ ∂B`.
2. `M` has even degree at every node ⇒ decompose into cycles ⇒ realize as polygons
   (their combined edge multiset is `M`; combined parity `= π_M`).
3. 1-D flip: along a transversal ray, `π_M(p) = 1_{A∩B}(p)` (status flips ⇔ M-edge crossed).
4. Common good ray existence (generalize `exists_good_dir` to the union of all vertices).

Fan-triangle realization (one triangle per `M`-edge from a common apex `O`) was ruled out:
spokes `(x,O)` pollute the boundary set and generically cross `A∩B`; only genuine cycle
realization keeps `Bd ⊆ ∂A∪∂B`.

## Build status (Lean files)
* `Geom.lean` ✓ — `vsub/cross/dot`, `mem_ray_iff`, `mem_seg_iff'`.
* `Telescope.lean` ✓ — `countP_zmod`, `cyclic_change_even`, `countP_parity_of_xor_even`.
* `Independence.lean` ✓ — `seg_mem_vertices`, `segments_countP_change_even` (cyclic).
* `Cross.lean` ✓ — `crossB_iff` (ray∩seg ⇔ sign-disjunction `Disj`).
* `CrossSigns.lean` ✓ — `parallel_extract`, `sign_fact` (gives `Ha1/Hb1/Ha2`), `sign_fact_K` (gives `HK`).
* `SectorCore.lean` (in progress) — pure-ℚ `sector_core`: `(Disj↔Disj)↔(Sect↔Sect)` given relation `o·K=c1b·c2a−c1a·c2b` + sign facts.
* `GoodRay.lean` (in progress) — `exists_good_dir`: a non-parallel vertex-avoiding rational direction exists.
* `RayIndep.lean` (next) — `per_edge` (crossB xor = statusB xor) via crossB_iff+sector_core+sign facts; `ray_indep`: o≠0 via per_edge+telescoping, o=0 via good-dir intermediary.

## Lemma inventory (build order)
0. Vector2D/ℚ algebra; `segment`/`ray` membership; `countP_append` parity.
1. Geometry primitives: side-of-ray test; "vertex-avoiding ray meets a segment in
   ≤1 pt, transversally"; sector status; crossing ⇔ status-toggle (per edge).
2. **Ray-independence** (Pillar 1) via telescoping.
3. `π_Q` well-defined; `interior_Q ∩ offEdges = {π_Q=1}`; additivity (Pillar 2).
4. Clipping: cut edges at `S`, inside/outside test constant per piece; build `M`.
5. Even-degree ⇒ cycle decomposition (induction, remove-a-cycle); realize as polys.
6. 1-D flip counting (Pillar 3) along a chosen transversal ray.
7. Final set-algebra assembly.

## Risks
* Pillar 1's per-edge geometric fact and Pillar 3's marching need careful ℚ-geometry.
* Pillar 5 (cycle decomposition + realization as Polygons) is algorithmic; the
  remove-a-cycle induction over a finite edge multiset is the plan.
* Choosing a transversal ray over ℚ avoiding finitely many bad directions: a bad
  direction set is finite, ℚ-directions are infinite ⇒ a good rational direction
  exists (pick slope avoiding finitely many values).
