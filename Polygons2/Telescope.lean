import Mathlib
import Polygons2.PolgonIntersection2Defs

/-!
# Telescoping: cyclic status-change count is even

Pure combinatorial backbone of ray-independence.  If `h : α → Bool` assigns a
status to each vertex, then walking the cyclic edge list of a polygon, the number
of edges whose endpoints have different status is even.
-/

open Classical
noncomputable section
namespace Polygons2

/-- Parity of `countP` as a sum of `ZMod 2` indicators. -/
lemma countP_zmod {α : Type*} (q : α → Bool) (l : List α) :
    (l.map (fun x => if q x then (1 : ZMod 2) else 0)).sum = (l.countP q : ZMod 2) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons, Nat.cast_add]
    by_cases h : q a = true
    · simp only [if_pos h, Nat.cast_one]; ring
    · simp only [if_neg h, Nat.cast_zero]; ring

/-- `xor` as `ZMod 2` addition of indicators. -/
lemma xor_indicator (a b : Bool) :
    (if (a != b) then (1 : ZMod 2) else 0)
      = (if a then (1 : ZMod 2) else 0) + (if b then (1 : ZMod 2) else 0) := by
  cases a <;> cases b <;> decide

/-- Sum of a pointwise sum over a list splits. -/
lemma sum_map_add {α : Type*} (f g : α → ZMod 2) (l : List α) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The core telescoping fact: along the cyclic edge list
`zip (v::vs) (vs ++ [v])`, the number of edges whose endpoints differ under `h`
is even. -/
lemma cyclic_change_even {α : Type*} (h : α → Bool) (v : α) (vs : List α) :
    ((List.zip (v :: vs) (vs ++ [v])).countP (fun p => h p.1 != h p.2)) % 2 = 0 := by
  set g : α → ZMod 2 := fun x => if h x then (1 : ZMod 2) else 0 with hg
  have hlen1 : (v :: vs).length ≤ (vs ++ [v]).length := by simp
  have hlen2 : (vs ++ [v]).length ≤ (v :: vs).length := by simp
  have key : ((List.zip (v :: vs) (vs ++ [v])).countP (fun p => h p.1 != h p.2) : ZMod 2) = 0 := by
    rw [← countP_zmod]
    have hpt : (fun p : α × α => if (h p.1 != h p.2) then (1 : ZMod 2) else 0)
             = (fun p : α × α => g p.1 + g p.2) := by
      funext p; rw [xor_indicator]
    rw [hpt, sum_map_add]
    have hfst : ((List.zip (v :: vs) (vs ++ [v])).map (fun p : α × α => g p.1)).sum
              = ((v :: vs).map g).sum := by
      rw [show (fun p : α × α => g p.1) = g ∘ Prod.fst from rfl, ← List.map_map,
        List.map_fst_zip hlen1]
    have hsnd : ((List.zip (v :: vs) (vs ++ [v])).map (fun p : α × α => g p.2)).sum
              = ((vs ++ [v]).map g).sum := by
      rw [show (fun p : α × α => g p.2) = g ∘ Prod.snd from rfl, ← List.map_map,
        List.map_snd_zip hlen2]
    rw [hfst, hsnd]
    have e1 : ((v :: vs).map g).sum = g v + (vs.map g).sum := by simp
    have e2 : ((vs ++ [v]).map g).sum = (vs.map g).sum + g v := by simp
    rw [e1, e2]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination (g v + (List.map g vs).sum) * h2
  have hdvd := (ZMod.natCast_eq_zero_iff _ 2).1 key
  omega

/-- If the number of elements where two Bool-predicates differ is even, then the two
`countP` values have equal parity. -/
lemma countP_parity_of_xor_even {α : Type*} (f g : α → Bool) (l : List α)
    (h : (l.countP (fun x => f x != g x)) % 2 = 0) :
    (l.countP f) % 2 = (l.countP g) % 2 := by
  have hf := countP_zmod f l
  have hg := countP_zmod g l
  have hx := countP_zmod (fun x => f x != g x) l
  have hfun : (fun x => (if f x then (1 : ZMod 2) else 0) + (if g x then (1 : ZMod 2) else 0))
            = (fun x => if (f x != g x) then (1 : ZMod 2) else 0) := by
    funext x; rw [xor_indicator]
  have key : ((l.countP f : ZMod 2) + (l.countP g : ZMod 2))
      = (l.countP (fun x => f x != g x) : ZMod 2) := by
    rw [← hf, ← hg, ← hx, ← sum_map_add, hfun]
  have hxz : (l.countP (fun x => f x != g x) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; omega
  rw [hxz] at key
  have h2 : (2 : ZMod 2) = 0 := by decide
  have heq : (l.countP f : ZMod 2) = (l.countP g : ZMod 2) := by
    linear_combination key - (l.countP g : ZMod 2) * h2
  have := (ZMod.natCast_eq_natCast_iff _ _ 2).1 heq
  simpa [Nat.ModEq] using this

end Polygons2
end
