import Mathlib

/-!
# Pairs-counting for the 1-D flip.

If `L1`, `L2` are lists of rationals with no common element, then
`Σ_{x∈L1} #{y∈L2: x<y}  +  Σ_{y∈L2} #{x∈L1: y<x} = |L1|·|L2|`
(every cross-pair has exactly one element beyond the other).
-/

open Classical
noncomputable section
namespace Polygons2

/-- Sum of `0/1` indicators equals `countP`. -/
lemma sum_ite_eq_countP {α : Type*} (q : α → Bool) (l : List α) :
    (l.map (fun x => if q x then (1 : ℕ) else 0)).sum = l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.countP_cons, ih]; ring

/-- `ℕ`-valued `sum`/`map` additivity. -/
lemma sum_map_add_nat {α : Type*} (f g : α → ℕ) (l : List α) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Additive predicates (on members) give additive `countP`. -/
lemma countP_add_of_pointwise {α : Type*} (p q r : α → Bool) (l : List α)
    (h : ∀ a ∈ l, (if p a then 1 else 0) + (if q a then 1 else 0) = (if r a then (1:ℕ) else 0)) :
    l.countP p + l.countP q = l.countP r := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    have ha := h a (List.mem_cons_self ..)
    have iht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    by_cases hp : p a <;> by_cases hq : q a <;> by_cases hr : r a <;> simp_all <;> omega

/-- Reindex a double count. -/
lemma sum_countP_swap (L1 L2 : List ℚ) :
    (L2.map (fun y => L1.countP (fun x => decide (y < x)))).sum
      = (L1.map (fun x => L2.countP (fun y => decide (y < x)))).sum := by
  induction L2 with
  | nil => simp
  | cons y t ih =>
    rw [List.map_cons, List.sum_cons, ih]
    rw [show (fun x => (y :: t).countP (fun z => decide (z < x)))
          = (fun x => (if decide (y < x) then 1 else 0) + t.countP (fun z => decide (z < x)))
        from funext (fun x => by rw [List.countP_cons]; ring)]
    rw [sum_map_add_nat, sum_ite_eq_countP (fun x => decide (y < x)) L1]

/-- The pairs-counting identity. -/
lemma pair_count (L1 L2 : List ℚ) (hdisj : ∀ x ∈ L1, ∀ y ∈ L2, x ≠ y) :
    (L1.map (fun x => L2.countP (fun y => decide (x < y)))).sum
      + (L2.map (fun y => L1.countP (fun x => decide (y < x)))).sum
      = L1.length * L2.length := by
  rw [sum_countP_swap L1 L2, ← sum_map_add_nat]
  have key : ∀ x ∈ L1,
      L2.countP (fun y => decide (x < y)) + L2.countP (fun y => decide (y < x)) = L2.length := by
    intro x hx
    rw [countP_add_of_pointwise (fun y => decide (x < y)) (fun y => decide (y < x))
        (fun _ => true) L2 ?_]
    · simp
    · intro y hy
      have hxy : x ≠ y := hdisj x hx y hy
      rcases lt_trichotomy x y with h | h | h
      · simp [h, not_lt.2 (le_of_lt h)]
      · exact absurd h hxy
      · simp [h, not_lt.2 (le_of_lt h)]
  rw [List.map_congr_left key, List.map_const', List.sum_replicate, smul_eq_mul]

end Polygons2
end
