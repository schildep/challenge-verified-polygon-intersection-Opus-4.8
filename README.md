# Formally verified polygon intersection construction challenge Opus 4.8

A challenge derived from [github.com/schildep/verified-polygon-intersection](https://github.com/schildep/verified-polygon-intersection) solved by Claude Opus 4.8 in ultracode mode in one shot. See previous commit for challenge template.

See [`prompt.txt`](prompt.txt).

I ran this in an isolated container to prevent peeking at the solution.

# Building and checking

```
lake build
```

```
printf 'import Polygons2.PolgonIntersection2\n#print axioms Polygons2.exists_polygons_inter_interior_eq_symmDiffAll_interiors_sdiff_boundaries\n' | lake env lean --stdin
```
Only depends on trusted axioms `[propext, Classical.choice, Quot.sound]`.
